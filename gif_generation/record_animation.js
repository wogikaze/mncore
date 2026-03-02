#!/usr/bin/env node
const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');
const puppeteer = require('puppeteer');

const TARGET_URL = process.env.MNCORE_VIEW_URL || 'http://localhost:4173/';
const TARGET_FILE = process.env.MNCORE_ANIM_FILE || 'DRAM→L2BM ingroup-bcast';
const TARGET_MOVIE = process.env.MNCORE_ANIM_MOVIE || null; // null => first movie
const OUT_DIR = process.env.MNCORE_FRAME_DIR || path.join(__dirname, 'gif_frames');
const GIF_ROOT = process.env.MNCORE_GIF_ROOT || path.join(__dirname, 'memory_animation_gifs');
const WIDTH = Number(process.env.MNCORE_VIEW_WIDTH || 1280);
const HEIGHT = Number(process.env.MNCORE_VIEW_HEIGHT || 720);
const RAW_SCALE = Number(process.env.MNCORE_CAPTURE_SCALE || 1);
const DEVICE_SCALE = Number.isFinite(RAW_SCALE) && RAW_SCALE > 0 ? RAW_SCALE : 1;
const FPS = Number(process.env.MNCORE_CAPTURE_FPS || 30);
const DURATION_MS = Number(process.env.MNCORE_CAPTURE_MS || 60000);
const PLAYBACK_SPEED = process.env.MNCORE_PLAYBACK_SPEED !== undefined
    ? Number(process.env.MNCORE_PLAYBACK_SPEED)
    : 0.25;
const END_THRESHOLD = process.env.MNCORE_END_THRESHOLD !== undefined
    ? Number(process.env.MNCORE_END_THRESHOLD)
    : 0.995;
const END_BUFFER_FRAMES = process.env.MNCORE_END_BUFFER_FRAMES !== undefined
    ? Number(process.env.MNCORE_END_BUFFER_FRAMES)
    : 15;
const KEEP_FRAMES = /^(1|true)$/i.test(process.env.MNCORE_KEEP_FRAMES || '0');
const CAPTURE_ALL = /^(1|true)$/i.test(process.env.MNCORE_CAPTURE_ALL || '0');
const SKIP_EXISTING = !/^(0|false)$/i.test(process.env.MNCORE_SKIP_EXISTING || '1');
const NAV_TIMEOUT = Number(process.env.MNCORE_NAV_TIMEOUT || 180000);

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

function slugify(text) {
    if (!text) return 'default';
    return text
        .replace(/→/g, '-to-')
        .toLowerCase()
        .replace(/[^0-9a-z]+/g, '_')
        .replace(/^_+|_+$/g, '') || 'item';
}

async function resetDir(dir) {
    await fs.promises.rm(dir, { recursive: true, force: true }).catch(() => { });
    await fs.promises.mkdir(dir, { recursive: true });
}

async function ensureParentDir(filePath) {
    await fs.promises.mkdir(path.dirname(filePath), { recursive: true });
}

function runCommand(command, args) {
    const result = spawnSync(command, args, { stdio: 'inherit' });
    if (result.status !== 0) {
        throw new Error(`${command} ${args.join(' ')} failed with code ${result.status}`);
    }
}

function runFfmpeg(framesPattern, fps, palettePath, gifPath) {
    runCommand('ffmpeg', ['-y', '-framerate', String(fps), '-i', framesPattern, '-vf', 'palettegen', palettePath]);
    runCommand('ffmpeg', ['-y', '-framerate', String(fps), '-i', framesPattern, '-i', palettePath, '-lavfi', 'paletteuse', gifPath]);
}

async function hasPlaybackEnded(page) {
    try {
        return page.evaluate((threshold) => {
            const slider = document.querySelector('#sb-main');
            if (!slider) return false;
            const value = Number(slider.value || 0);
            return Number.isFinite(value) && value >= threshold;
        }, END_THRESHOLD);
    } catch {
        return false;
    }
}

async function preparePage(page) {
    await page.goto(TARGET_URL, { waitUntil: 'networkidle2', timeout: NAV_TIMEOUT });
    await page.waitForSelector('select', { timeout: NAV_TIMEOUT });
}

async function selectByText(page, selectIndex, targetText) {
    return page.evaluate(({ selectIndex, targetText }) => {
        const selects = document.querySelectorAll('select');
        const select = selects[selectIndex];
        if (!select) throw new Error(`select ${selectIndex} not found`);
        const options = Array.from(select.options);
        const trimmed = targetText ? targetText.trim() : null;
        let match = null;
        if (trimmed) {
            match = options.find((opt) => opt.text.trim() === trimmed);
        }
        if (!match) {
            match = options.find((opt) => opt.value && opt.text.trim());
        }
        if (!match) {
            match = options.find((opt) => opt.text && opt.text.trim());
        }
        if (!match) throw new Error(`option not found for ${trimmed}`);
        select.value = match.value;
        select.dispatchEvent(new Event('input', { bubbles: true }));
        select.dispatchEvent(new Event('change', { bubbles: true }));
        return match.text.trim();
    }, { selectIndex, targetText });
}

async function waitForMovieOptions(page) {
    try {
        await page.waitForFunction(() => {
            const selects = document.querySelectorAll('select');
            const movieSelect = selects[1];
            if (!movieSelect) return false;
            return Array.from(movieSelect.options).some((opt) => !!opt.value);
        }, { timeout: 60000 });
        return true;
    } catch (err) {
        console.warn('Timed out waiting for movie options:', err.message);
        return false;
    }
}

async function listFileNames(page) {
    return page.evaluate(() => {
        const select = document.querySelectorAll('select')[0];
        if (!select) return [];
        return Array.from(select.options)
            .map((opt) => opt.text.trim())
            .filter(Boolean);
    });
}

async function listMovieNames(page, fileName) {
    await selectByText(page, 0, fileName);
    const hasMovies = await waitForMovieOptions(page);
    if (!hasMovies) {
        return [];
    }
    return page.evaluate(() => {
        const movieSelect = document.querySelectorAll('select')[1];
        if (!movieSelect) return [];
        return Array.from(movieSelect.options)
            .filter((opt) => opt.value)
            .map((opt) => opt.text.trim())
            .filter(Boolean);
    });
}

async function setPlaybackSpeed(page, speed) {
    const targetSpeed = Math.min(1, Math.max(0, Number.isNaN(speed) ? 0.25 : speed));
    await page.evaluate((value) => {
        const slider = document.querySelector('#sb-speed');
        if (!slider) {
            throw new Error('speed slider not found');
        }
        slider.value = String(value);
        slider.dispatchEvent(new Event('input', { bubbles: true }));
        slider.dispatchEvent(new Event('change', { bubbles: true }));
    }, targetSpeed);
    return targetSpeed;
}

async function captureSingle(page, { fileName, movieName, framesDir, autoConvert, gifPath }) {
    await preparePage(page);
    console.log('Selected file:', await selectByText(page, 0, fileName));
    const hasMovies = await waitForMovieOptions(page);
    if (!hasMovies) {
        console.warn('Movie list did not populate; using default entry.');
    }
    console.log('Selected movie:', await selectByText(page, 1, movieName));
    await page.waitForSelector('#sb-play');
    const speed = await setPlaybackSpeed(page, PLAYBACK_SPEED);
    console.log('Playback speed set to', speed.toFixed(2));
    await page.click('#sb-play');
    console.log('Playback started');

    await resetDir(framesDir);
    const canvasHandle = await page.$('#canvas');
    if (!canvasHandle) throw new Error('Canvas not found');
    const interval = 1000 / FPS;
    const totalFrames = Math.floor(DURATION_MS / interval);
    const trailingBuffer = Number.isFinite(END_BUFFER_FRAMES) ? Math.max(0, Math.floor(END_BUFFER_FRAMES)) : 0;
    let trailingFramesLeft = null;
    let capturedFrames = 0;
    for (let i = 0; i < totalFrames; i++) {
        const dataUrl = await page.evaluate((canvas) => canvas.toDataURL('image/png'), canvasHandle);
        const buffer = Buffer.from(dataUrl.split(',')[1], 'base64');
        const filename = path.join(framesDir, `frame_${String(i).padStart(4, '0')}.png`);
        await fs.promises.writeFile(filename, buffer);
        capturedFrames = i + 1;
        process.stdout.write(`Captured ${capturedFrames}/${totalFrames}\r`);

        if (trailingFramesLeft !== null) {
            if (trailingFramesLeft <= 0) {
                console.log('\nTrailing frame capture complete.');
                break;
            }
        } else if (await hasPlaybackEnded(page)) {
            trailingFramesLeft = trailingBuffer;
            console.log(`\nDetected playback completion at frame ${capturedFrames}. Capturing ${trailingBuffer} trailing frame(s).`);
            if (trailingFramesLeft <= 0) {
                console.log('Trailing frame capture complete.');
                break;
            }
        }

        if (typeof page.waitForTimeout === 'function') {
            await page.waitForTimeout(interval);
        } else {
            await sleep(interval);
        }

        if (trailingFramesLeft !== null) {
            trailingFramesLeft -= 1;
        }
    }
    console.log(`\nCaptured ${capturedFrames} frames`);

    if (autoConvert && capturedFrames > 0) {
        await ensureParentDir(gifPath);
        const palettePath = path.join(framesDir, 'palette.png');
        runFfmpeg(path.join(framesDir, 'frame_%04d.png'), FPS, palettePath, gifPath);
        console.log('GIF written to', gifPath);
        if (!KEEP_FRAMES) {
            await fs.promises.rm(framesDir, { recursive: true, force: true }).catch(() => { });
        }
    }
}

async function captureAll(page) {
    await preparePage(page);
    const fileNames = await listFileNames(page);
    console.log(`Found ${fileNames.length} animation file(s).`);
    let totalTargets = 0;
    const tasks = [];
    for (const fileName of fileNames) {
        const movies = await listMovieNames(page, fileName);
        const targets = movies.length ? movies : [null];
        totalTargets += targets.length;
        tasks.push({ fileName, movies: targets });
    }
    console.log(`Capturing ${totalTargets} movie variation(s).`);

    let completed = 0;
    for (const task of tasks) {
        const fileSlug = slugify(task.fileName);
        for (const movieName of task.movies) {
            const movieSlug = slugify(movieName || 'default');
            const framesDir = path.join(OUT_DIR, fileSlug, movieSlug);
            const gifPath = path.join(GIF_ROOT, fileSlug, `${movieSlug}.gif`);
            const ordinal = completed + 1;
            if (SKIP_EXISTING && fs.existsSync(gifPath)) {
                console.log(`\n[${ordinal}/${totalTargets}] ${task.fileName} :: ${movieName || 'default'} (skip existing)`);
                completed += 1;
                continue;
            }
            console.log(`\n[${ordinal}/${totalTargets}] ${task.fileName} :: ${movieName || 'default'}`);
            await captureSingle(page, { fileName: task.fileName, movieName, framesDir, autoConvert: true, gifPath });
            completed += 1;
        }
    }
}

(async () => {
    const viewportWidth = Math.round(WIDTH);
    const viewportHeight = Math.round(HEIGHT);
    const browser = await puppeteer.launch({
        headless: 'new',
        defaultViewport: { width: viewportWidth, height: viewportHeight, deviceScaleFactor: DEVICE_SCALE },
        args: [
            `--window-size=${viewportWidth},${viewportHeight}`,
            '--use-gl=swiftshader',
            '--use-angle=swiftshader',
            '--enable-software-rasterizer',
            '--enable-unsafe-swiftshader',
            '--enable-webgl',
            '--ignore-gpu-blocklist',
            '--hide-scrollbars',
            '--no-sandbox',
            '--disable-setuid-sandbox'
        ],
    });

    try {
        const page = await browser.newPage();
        console.log(`Viewport ${viewportWidth}x${viewportHeight} @ ${DEVICE_SCALE.toFixed(2)}x scale`);
        page.setDefaultNavigationTimeout(NAV_TIMEOUT);
        page.setDefaultTimeout(NAV_TIMEOUT);
        page.on('console', (msg) => console.log('[page]', msg.type(), msg.text()));
        page.on('pageerror', (err) => console.error('[page-error]', err));

        if (CAPTURE_ALL) {
            await fs.promises.mkdir(GIF_ROOT, { recursive: true });
            await captureAll(page);
        } else {
            await resetDir(OUT_DIR);
            await captureSingle(page, { fileName: TARGET_FILE, movieName: TARGET_MOVIE, framesDir: OUT_DIR, autoConvert: false });
        }
    } finally {
        await browser.close();
    }
})();
