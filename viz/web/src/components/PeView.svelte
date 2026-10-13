<script lang="ts">
  import gsap from 'gsap';
  import { app } from '../lib/state.svelte';
  import { format, hex } from '../lib/numbers';
  import { read, type Memory } from '../lib/memory';
  import type { Access, LineInfo } from '../lib/types';

  const W = 1000;
  const H = 384;
  const COL = W / 4;
  const CELLS = 6;
  const CELL_W = (COL - 58) / CELLS;
  const ROWS = [
    { loc: 'grf0', label: 'GRF0 $r' },
    { loc: 'grf1', label: 'GRF1 $s' },
    { loc: 't', label: 'T $t' },
    { loc: 'lm0', label: 'LM0 $m' },
    { loc: 'lm1', label: 'LM1 $n' },
  ];
  const ROW_Y = (r: number) => 24 + r * 32;
  const UNIT_Y = 192;
  const FWD_Y = 236;
  const MAT_Y = 282;

  const trace = $derived(app.trace);
  const line = $derived<LineInfo | undefined>(trace?.lines[app.line]);
  const pes = $derived(trace?.focus ?? [0, 1, 2, 3]);

  /** Words (word addresses; for T: cycle * 4 + i) shown in each row of each PE. */
  const shown = $derived.by(() => {
    const out = new Map<string, number[]>();
    if (!trace) return out;
    for (const pe of pes) {
      for (const { loc } of ROWS) {
        const set = new Set<number>();
        const add = (a: Access) => {
          if (a.unit !== pe || a.loc !== loc || a.addr === null) return;
          if (loc === 't') {
            set.add(a.addr * 4);
            set.add(a.addr * 4 + 1);
          } else a.words.forEach((_, i) => set.add(a.addr! + i));
        };
        // This line's accesses first, then the most recent earlier ones.
        line?.accesses.forEach(add);
        for (let i = app.line - 1; i >= 0 && set.size < CELLS; i--) trace.lines[i].accesses.forEach(add);
        if (set.size < CELLS) trace.init.forEach(add);
        if (app.selection && app.selection.unit === pe && app.selection.loc === loc) set.add(app.selection.addr);
        const sorted = [...set].sort((a, b) => a - b).slice(0, CELLS);
        out.set(`${pe}:${loc}`, sorted);
      }
    }
    return out;
  });

  function cellPos(pe: number, loc: string, word: number): { x: number; y: number } | null {
    const col = pes.indexOf(pe);
    const r = ROWS.findIndex((x) => x.loc === loc);
    const list = shown.get(`${pe}:${loc}`) ?? [];
    const k = list.indexOf(word);
    if (col < 0 || r < 0 || k < 0) return null;
    return { x: col * COL + 54 + k * CELL_W + CELL_W / 2, y: ROW_Y(r) + 13 };
  }
  const unitPos = (pe: number, unit: string) => {
    const col = Math.max(0, pes.indexOf(pe));
    if (unit === 'matrix' || unit === 'mwrite' || unit === 'mread') return { x: W / 2, y: MAT_Y + 46 };
    if (unit === 'l1-to-pe' || unit === 'pe-to-l1' || unit === 'l2') return { x: W - 90, y: MAT_Y + 26 };
    return { x: col * COL + (unit === 'mau' ? COL * 0.68 : COL * 0.3), y: UNIT_Y + 16 };
  };
  const fwdPos = (pe: number, loc: string) => {
    const col = Math.max(0, pes.indexOf(pe));
    const k = ['aluf', 'mauf', 'mreadf', 'lbf'].indexOf(loc);
    return { x: col * COL + 30 + k * ((COL - 40) / 4) + (COL - 40) / 8, y: FWD_Y + 12 };
  };

  // Show the state before the line while it animates, then the state after it.
  let settled = $state(false);
  const mem = $derived<Memory>(settled ? app.after : app.before);

  function cellText(pe: number, loc: string, word: number): string {
    const v = read(mem, `pe:${pe}`, loc, word);
    if (v === undefined) return '·';
    if (app.view === 'f64') {
      if (word % 2) return '';
      const lo = read(mem, `pe:${pe}`, loc, word + 1) ?? 0;
      return format([v, lo], 'f64')[0];
    }
    if (app.view === 'f16') return format([v], 'f16').join(' ');
    return format([v], app.view)[0];
  }

  // Changed cells in this line, highlighted after the animation.
  const written = $derived.by(() => {
    const s = new Set<string>();
    for (const a of line?.accesses ?? []) {
      if (!a.write || a.addr === null || a.loc === 'out') continue;
      if (a.loc === 't') {
        s.add(`${a.unit}:t:${a.addr * 4}`);
        s.add(`${a.unit}:t:${a.addr * 4 + 1}`);
      } else a.words.forEach((_, i) => s.add(`${a.unit}:${a.loc}:${a.addr! + i}`));
    }
    return s;
  });

  // Latest forwarded values (cycle 0) of each focus PE, for the forwarding boxes.
  const fwdValues = $derived.by(() => {
    const out = new Map<string, number[]>();
    if (!trace) return out;
    const upto = settled ? app.line : app.line - 1;
    for (let i = upto; i >= 0 && out.size < pes.length * 4; i--) {
      const l = trace.lines[i];
      if (l.kind !== 'pe') continue;
      l.exprs.forEach((e, ei) => {
        if (!e.fwd) return;
        for (const pe of pes) {
          const key = `${pe}:${e.fwd}`;
          if (out.has(key)) continue;
          const o = l.accesses.find((a) => a.loc === 'out' && a.expr === ei && a.unit === pe && a.cycle === 0);
          if (o) out.set(key, o.words);
        }
      });
    }
    return out;
  });

  // Matrix register rows written in this line.
  const matWritten = $derived.by(() => {
    const s = new Set<string>();
    if (!settled) return s;
    for (const a of line?.accesses ?? []) if (a.loc === 'matx' || a.loc === 'maty') s.add(`${a.loc}:${a.addr}`);
    return s;
  });

  /** Color of a matrix register word: hue by sign, lightness by exponent. */
  function heat(v: number | undefined): string {
    if (v === undefined || v === 0) return 'var(--panel)';
    const exp = (v >>> 23) & 0xff;
    const t = Math.min(1, Math.abs(exp - 127) / 40);
    const hue = v >>> 31 ? 210 : 25;
    return `hsl(${hue} 70% ${70 - t * 35}%)`;
  }

  let layer: SVGGElement | undefined = $state();
  let tl: gsap.core.Timeline | null = null;

  $effect(() => {
    const l = line;
    const seconds = app.stepSeconds * Math.min(l?.words || 1, 4) * 0.9;
    void app.view;
    if (!layer) return;
    tl?.kill();
    layer.replaceChildren();
    settled = false;
    if (!l || l.kind !== 'pe' || l.accesses.length === 0) {
      settled = true;
      return;
    }
    const cycleDur = seconds / 4;
    const ns = 'http://www.w3.org/2000/svg';
    tl = gsap.timeline({ onComplete: () => (settled = true) });
    const token = (from: { x: number; y: number }, to: { x: number; y: number }, label: string, cls: string, at: number) => {
      const g = document.createElementNS(ns, 'g');
      g.setAttribute('class', `token ${cls}`);
      const r = document.createElementNS(ns, 'rect');
      r.setAttribute('x', '-20');
      r.setAttribute('y', '-7');
      r.setAttribute('width', '40');
      r.setAttribute('height', '14');
      r.setAttribute('rx', '3');
      const t = document.createElementNS(ns, 'text');
      t.setAttribute('y', '3.5');
      t.textContent = label;
      g.append(r, t);
      layer!.appendChild(g);
      tl!.fromTo(g, { x: from.x, y: from.y, opacity: 0 }, { x: to.x, y: to.y, opacity: 1, duration: cycleDur * 0.45, ease: 'power2.inOut' }, at);
      tl!.to(g, { opacity: 0, duration: cycleDur * 0.2 }, at + cycleDur * 0.6);
    };
    const short = (words: number[]) => (words.length ? (app.view === 'hex' ? hex(words[0]).slice(0, 6) : format(words.slice(0, app.view === 'f64' ? 2 : 1), app.view)[0]) : '');
    for (const a of l.accesses) {
      const unit = l.exprs[a.expr]?.unit ?? 'alu';
      const at = a.cycle * cycleDur;
      if (a.loc === 'out') {
        // Result of the unit in this cycle.
        const p = unitPos(a.unit, unit);
        token(p, { x: p.x, y: p.y - 14 }, short(a.words), 'out', at + cycleDur * 0.35);
        continue;
      }
      if (a.loc === 'l1bm' || a.loc === 'matx' || a.loc === 'maty') {
        const p = unitPos(a.unit * 4, a.loc === 'l1bm' ? 'pe-to-l1' : 'mwrite');
        token({ x: p.x, y: p.y - 30 }, p, short(a.words), 'block', at + cycleDur * 0.5);
        continue;
      }
      const isFwd = a.loc === 'aluf' || a.loc === 'mauf' || a.loc === 'mreadf' || a.loc === 'lbf';
      const memWord = a.addr === null ? null : a.loc === 't' ? a.addr * 4 : a.addr;
      const place = isFwd ? fwdPos(a.unit, a.loc) : memWord !== null ? cellPos(a.unit, a.loc, memWord) : null;
      if (!place) continue;
      const u = unitPos(a.unit, unit);
      if (a.write) token(u, place, short(a.words), 'write', at + cycleDur * 0.5);
      else token(place, u, short(a.words), 'read', at);
    }
  });

  function select(pe: number, loc: string, word: number) {
    app.selection = { unit: pe, loc, addr: word };
  }
</script>

<section class="pe">
  <header>
    <span>注目 MAB の内部（PE {pes[0]}〜{pes[pes.length - 1]}）</span>
    <label>
      表示
      <select bind:value={app.view}>
        <option value="f32">単精度</option>
        <option value="f64">倍精度</option>
        <option value="f16">半精度 (1/6/9)</option>
        <option value="i32">整数</option>
        <option value="hex">16進</option>
      </select>
    </label>
    <label>
      注目 PE
      <input type="number" min="0" max="4095" step="4" value={app.focusPe} onchange={(e) => { app.focusPe = +(e.currentTarget as HTMLInputElement).value; app.simulate(); }} />
    </label>
  </header>
  <svg viewBox="0 0 {W} {H}" preserveAspectRatio="xMidYMin meet">
    {#each pes as pe, col}
      <g transform="translate({col * COL}, 0)">
        <text class="pehead" x="6" y="16">PE{pe % 4}（#{pe}）</text>
        {#each ROWS as row, r}
          <text class="rowlabel" x="6" y={ROW_Y(r) + 16}>{row.label}</text>
          {#each shown.get(`${pe}:${row.loc}`) ?? [] as word, k}
            {@const key = `${pe}:${row.loc}:${word}`}
            <g
              class="cell"
              class:written={settled && written.has(key)}
              class:selected={app.selection?.unit === pe && app.selection?.loc === row.loc && app.selection?.addr === word}
              transform="translate({54 + k * CELL_W}, {ROW_Y(r)})"
              role="button"
              tabindex="0"
              onclick={() => select(pe, row.loc, word)}
              onkeydown={(e) => e.key === 'Enter' && select(pe, row.loc, word)}
            >
              <rect width={CELL_W - 2} height="26" rx="2" />
              <text class="addr" x="2" y="8">{row.loc === 't' ? `c${Math.floor(word / 4)}.${word % 4}` : word}</text>
              <text class="val" x={(CELL_W - 2) / 2} y="21">{cellText(pe, row.loc, word)}</text>
            </g>
          {/each}
        {/each}
        <g transform="translate({COL * 0.3 - 40}, {UNIT_Y})">
          <rect class="unit alu" width="80" height="32" rx="6" />
          <text x="40" y="20">ALU</text>
        </g>
        <g transform="translate({COL * 0.68 - 40}, {UNIT_Y})">
          <rect class="unit mau" width="80" height="32" rx="6" />
          <text x="40" y="20">MAU</text>
        </g>
        {#each ['aluf', 'mauf', 'mreadf', 'lbf'] as f, k}
          {@const v = fwdValues.get(`${pe}:${f}`)}
          <g transform="translate({30 + k * ((COL - 40) / 4)}, {FWD_Y})">
            <rect class="fwd" width={(COL - 40) / 4 - 4} height="24" rx="3" />
            <text class="addr" x="3" y="8">${f}</text>
            <text class="val" x={((COL - 40) / 4 - 4) / 2} y="19">{v ? format(v.slice(0, app.view === 'f64' ? 2 : 1), app.view)[0] : '·'}</text>
          </g>
        {/each}
      </g>
    {/each}
    <g transform="translate({W / 2 - 250}, {MAT_Y})">
      <rect class="unit matrix" width="500" height="90" rx="6" />
      <text x="250" y="14">行列レジスタ（MAB 共通）: mwrite で書き、mfma / mmul で使い、mread で転置して読む</text>
      {#each ['matx', 'maty'] as side, si}
        <text class="sub" x={20 + si * 245} y="50">${side === 'matx' ? 'x' : 'y'}</text>
        {#each Array(16) as _, row}
          {#each Array(8) as _, w}
            {@const v = read(mem, `mab:${Math.floor(pes[0] / 4)}`, side, row * 8 + w)}
            <rect
              class="mcell"
              class:mwritten={matWritten.has(`${side}:${row}`)}
              x={34 + si * 245 + row * 12.5}
              y={22 + w * 8}
              width="11.5"
              height="7"
              style:fill={heat(v)}
            >
              <title>{side} 物理行 {row} 語 {w}: {v === undefined ? '0' : format([v], app.view)[0]}</title>
            </rect>
          {/each}
        {/each}
      {/each}
    </g>
    <g transform="translate({W - 170}, {MAT_Y})">
      <rect class="unit l1" width="160" height="90" rx="6" />
      <text x="80" y="22">L1BM（L1B {Math.floor(pes[0] / 64)}）</text>
      <text class="sub" x="80" y="40">放送・分配・収集・縮約</text>
    </g>
    <g bind:this={layer}></g>
  </svg>
</section>

<style>
  .pe {
    display: flex;
    flex-direction: column;
    min-height: 0;
  }
  header {
    display: flex;
    gap: 16px;
    align-items: center;
    padding: 4px 8px;
    font-size: 12px;
    color: var(--muted);
  }
  header span {
    margin-right: auto;
  }
  header input {
    width: 5em;
  }
  svg {
    width: 100%;
    flex: 1;
    min-height: 0;
  }
  text {
    font-size: 10px;
    fill: var(--fg);
  }
  .pehead {
    font-weight: 600;
    font-size: 12px;
  }
  .rowlabel {
    fill: var(--muted);
    font-size: 9px;
    font-family: var(--mono);
  }
  .cell {
    cursor: pointer;
  }
  .cell rect {
    fill: var(--panel);
    stroke: var(--line);
  }
  .cell.written rect {
    fill: color-mix(in srgb, var(--accent) 22%, var(--panel));
  }
  .cell.selected rect {
    stroke: var(--accent);
    stroke-width: 2;
  }
  .addr {
    font-size: 8px;
    fill: var(--muted);
    font-family: var(--mono);
  }
  .val {
    font-size: 10px;
    text-anchor: middle;
    font-family: var(--mono);
  }
  .unit {
    stroke: var(--line);
  }
  .unit + text,
  .sub {
    text-anchor: middle;
  }
  .sub {
    font-size: 9px;
    fill: var(--muted);
  }
  .alu {
    fill: color-mix(in srgb, var(--c-compute) 18%, var(--panel));
  }
  .mau {
    fill: color-mix(in srgb, var(--c-mau) 18%, var(--panel));
  }
  .matrix {
    fill: color-mix(in srgb, var(--c-mau) 10%, var(--panel));
  }
  .l1 {
    fill: color-mix(in srgb, var(--c-l1) 14%, var(--panel));
  }
  .mcell {
    stroke: none;
  }
  .mcell.mwritten {
    stroke: var(--fg);
    stroke-width: 1;
  }
  .fwd {
    fill: var(--panel);
    stroke: var(--line);
    stroke-dasharray: 2 2;
  }
  :global(.token rect) {
    fill: var(--fg);
  }
  :global(.token text) {
    fill: var(--bg);
    font-size: 8px;
    text-anchor: middle;
    font-family: var(--mono);
  }
  :global(.token.write rect) {
    fill: var(--accent);
  }
  :global(.token.out rect) {
    fill: var(--c-mau);
  }
  :global(.token.block rect) {
    fill: var(--c-l1);
  }
</style>
