<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { player } from '../lib/player.svelte';
  import { volume } from '../lib/numbers';
  import { CATEGORY_COLORS, CATEGORY_NAMES, category } from '../lib/flows';

  const W = 1000;
  const H = 44;
  const trace = $derived(app.trace);

  const bars = $derived.by(() => {
    if (!trace) return [];
    const total = Math.max(1, trace.score);
    return trace.lines.flatMap((l, i) => {
      if (!l.words) return [];
      const sums: Record<string, number> = {};
      for (const f of l.flows) {
        const c = category(f.from, f.to);
        sums[c] = (sums[c] ?? 0) + f.longs;
      }
      const x = (l.step / total) * W;
      const w = Math.max(0.8, (l.words / total) * W - 0.4);
      let y = H - 4;
      const parts = Object.entries(sums).map(([c, v]) => {
        const h = Math.min(24, 4 + Math.log2(1 + v) * 1.1);
        y -= h;
        return { c, y, h, v };
      });
      return [{ i, x, w, parts, nop: l.kind === 'nop' }];
    });
  });

  const ticks = $derived.by(() => {
    const total = trace?.score ?? 0;
    if (!total) return [];
    const step = total <= 16 ? 1 : total <= 40 ? 5 : total <= 100 ? 10 : 20;
    const out: { s: number; x: number }[] = [];
    for (let s = 0; s <= total; s += step) out.push({ s, x: (s / total) * W });
    return out;
  });

  const cursor = $derived.by(() => {
    if (!trace) return 0;
    const l = trace.lines[app.line];
    return ((l?.step ?? 0) / Math.max(1, trace.score)) * W;
  });

  const current = $derived(trace?.lines[app.line]);

  let svg: SVGSVGElement | undefined = $state();
  let dragging = false;
  function seekAt(ev: PointerEvent) {
    if (!trace || !svg) return;
    const r = svg.getBoundingClientRect();
    const step = ((ev.clientX - r.left) / r.width) * trace.score;
    let best = 0;
    trace.lines.forEach((l, i) => {
      if (l.words && l.step <= step) best = i;
    });
    app.seek(best);
    player.progress = 1;
  }

  function nextLine(): number {
    let i = app.line + 1;
    while (trace && i < trace.lines.length - 1 && trace.lines[i].words === 0) i++;
    return i;
  }

  function onKey(ev: KeyboardEvent) {
    if ((ev.target as HTMLElement).tagName === 'TEXTAREA') return;
    if (ev.key === 'ArrowRight') {
      if (ev.shiftKey) player.nextCycle();
      else {
        player.pause();
        player.goto(app.line + 1 < (trace?.lines.length ?? 0) ? nextLine() : app.line);
      }
    } else if (ev.key === 'ArrowLeft') {
      if (ev.shiftKey) player.prevCycle();
      else {
        player.pause();
        app.prev();
        player.progress = 1;
      }
    } else if (ev.key === ' ') {
      player.toggle();
      ev.preventDefault();
    }
  }
</script>

<svelte:window onkeydown={onKey} />

<section class="timeline">
  <div class="controls">
    <div class="transport">
      <button onclick={() => { player.pause(); app.prev(); player.progress = 1; }} title="前の行 (←)">⏮</button>
      <button onclick={() => player.prevCycle()} title="前のサイクル (Shift+←)">◀</button>
      <button class="play" onclick={() => player.toggle()} title="再生 / 停止 (Space)">{player.playing ? '❚❚' : '▶'}</button>
      <button onclick={() => player.nextCycle()} title="次のサイクル (Shift+→)">▶</button>
      <button onclick={() => { player.pause(); player.goto(nextLine()); }} title="次の行 (→)">⏭</button>
    </div>
    <label class="speed" title="1ステップあたりの秒数">
      速度 <input type="range" min="0.2" max="3" step="0.1" bind:value={app.stepSeconds} />
      <span>{app.stepSeconds.toFixed(1)}s</span>
    </label>
    {#if trace}
      <span class="pos">
        <b>{current?.lineno}</b>行目・step <b>{current?.step ?? 0}</b> / {trace.score}
        {#if current?.kind === 'nop'}<span class="nop">NOP</span>{/if}
        {#if current?.kind === 'mv'}<span class="mv">MV</span>{/if}
      </span>
      <span class="cycle">サイクル {player.progress >= 1 ? '—' : player.cycle}</span>
      <span class="legend">
        {#each Object.entries(CATEGORY_COLORS) as [c, col]}
          <i style:background={col}></i>{CATEGORY_NAMES[c]}
        {/each}
      </span>
    {/if}
  </div>

  <svg
    bind:this={svg}
    viewBox="0 0 {W} {H}"
    preserveAspectRatio="none"
    role="slider"
    aria-label="ステップ"
    aria-valuenow={app.line}
    tabindex="0"
    onpointerdown={(e) => {
      dragging = true;
      (e.currentTarget as Element).setPointerCapture(e.pointerId);
      player.pause();
      seekAt(e);
    }}
    onpointermove={(e) => dragging && seekAt(e)}
    onpointerup={() => (dragging = false)}
  >
    <rect class="bg" x="0" y="0" width={W} height={H} />
    {#each ticks as t}
      <line class="grid" x1={t.x} x2={t.x} y1="0" y2={H} />
      <text class="tick" x={t.x + 2} y="9">{t.s}</text>
    {/each}
    {#each bars as b (b.i)}
      {#if b.nop}<rect x={b.x} y="0" width={b.w} height={H} class="nopband" />{/if}
      {#each b.parts as p}
        <rect class="bar" x={b.x} y={p.y} width={b.w} height={p.h} fill={CATEGORY_COLORS[p.c]}>
          <title>{volume(p.v)}</title>
        </rect>
      {/each}
    {/each}
    <line class="cursor" x1={cursor} x2={cursor} y1="0" y2={H} />
  </svg>
</section>

<style>
  .timeline {
    height: 100%;
    display: flex;
    flex-direction: column;
    padding: 3px 10px 5px;
    gap: 2px;
    background: var(--panel);
  }
  .controls {
    display: flex;
    align-items: center;
    gap: 10px;
    font-size: 11px;
    min-height: 30px;
    flex-wrap: wrap;
  }
  .transport {
    display: flex;
    gap: 2px;
  }
  .transport button {
    min-width: 28px;
    height: 24px;
    padding: 0 5px;
    font-size: 11px;
  }
  .transport .play {
    min-width: 36px;
    border-color: var(--accent);
    color: var(--accent);
  }
  .speed {
    display: flex;
    align-items: center;
    gap: 4px;
    color: var(--muted);
  }
  .speed input {
    width: 90px;
    padding: 0;
  }
  .speed span {
    font-family: var(--mono);
    width: 28px;
  }
  .pos {
    font-family: var(--mono);
    color: var(--muted);
    white-space: nowrap;
  }
  .pos b {
    color: var(--fg);
    font-size: 13px;
  }
  .nop {
    color: var(--warn);
    margin-left: 4px;
  }
  .mv {
    color: var(--c-offchip);
    margin-left: 4px;
  }
  .cycle {
    font-family: var(--mono);
    color: var(--muted);
    white-space: nowrap;
  }
  .legend {
    margin-left: auto;
    display: flex;
    gap: 4px;
    align-items: center;
    color: var(--muted);
    white-space: nowrap;
  }
  .legend i {
    display: inline-block;
    width: 7px;
    height: 7px;
    border-radius: 2px;
    margin-left: 6px;
  }
  svg {
    width: 100%;
    flex: 1;
    min-height: 30px;
    max-height: 44px;
    cursor: pointer;
    touch-action: none;
  }
  .bg {
    fill: var(--panel-2);
  }
  .grid {
    stroke: var(--line);
    stroke-width: 0.6;
  }
  .tick {
    font-family: var(--mono);
    font-size: 10px;
    fill: var(--muted);
  }
  .bar {
    opacity: 0.78;
  }
  .nopband {
    fill: var(--warn);
    opacity: 0.18;
  }
  .cursor {
    stroke: var(--fg);
    stroke-width: 2;
    vector-effect: non-scaling-stroke;
  }
</style>
