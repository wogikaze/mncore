<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { player } from '../lib/player.svelte';
  import { format } from '../lib/numbers';
  import { read } from '../lib/memory';
  import type { Access, ExprInfo, LineInfo } from '../lib/types';

  // One PE's data path for the current step, unrolled left to right:
  // sources (memory rows read, forwarding registers, L1BM, matrix register)
  // -> one box per expression (input pins, output pin) -> destinations.

  const W = 1100;
  const SRC_X = 10;
  const SRC_W = 300;
  const UNIT_X = 430;
  const UNIT_W = 230;
  const DST_X = 790;
  const DST_W = 300;
  const ROW_H = 20;
  const HEAD_H = 22;
  const GAP = 12;

  const trace = $derived(app.trace);
  const line = $derived<LineInfo | undefined>(trace?.lines[app.line]);
  const pes = $derived(trace?.focus ?? [0, 1, 2, 3]);
  let peIdx = $state(0);
  const pe = $derived(pes[Math.min(peIdx, pes.length - 1)] ?? 0);
  const mab = $derived(Math.floor(pe / 4));
  const l1b = $derived(Math.floor(pe / 64));
  /** Cycle to emphasize; null shows all cycles alike. */
  let pinned = $state<number | null>(null);
  const cycle = $derived(player.playing || player.progress < 1 ? player.cycle : pinned);

  const MEM_NAME: Record<string, string> = {
    grf0: 'GRF0 ($r)',
    grf1: 'GRF1 ($s)',
    t: 'T レジスタ ($t)',
    lm0: 'LM0 ($m)',
    lm1: 'LM1 ($n)',
    aluf: '$aluf（前ステップの ALU 結果）',
    mauf: '$mauf（前ステップの MAU 結果）',
    mreadf: '$mreadf（前ステップの転置読出し）',
    lbf: '$lbf（前ステップの L1BM 転送）',
    l1bm_src: 'L1BM',
    matrix: '行列レジスタ',
  };
  const UNIT_NAME: Record<string, string> = {
    alu: 'ALU',
    mau: 'MAU ベクトル演算',
    matrix: 'MAU 行列ベクトル積',
    mwrite: '行列レジスタ書き込み',
    mread: '行列レジスタ転置読み出し',
    'l1-to-pe': 'L1BM → PE 転送',
    'pe-to-l1': 'PE → L1BM 転送',
    l2: 'L2BM ↔ L1BM 転送',
  };

  interface Row {
    key: string;
    addr: number | null;
    label: string;
    accesses: Access[];
    y: number;
  }
  interface Block {
    key: string;
    title: string;
    rows: Row[];
    y: number;
    h: number;
  }
  interface UnitBox {
    expr: number;
    info: ExprInfo;
    y: number;
    h: number;
    pins: { label: string; y: number }[];
    outY: number;
    outs: Access[];
  }
  interface Wire {
    d: string;
    kind: 'read' | 'write';
    cycle: number;
    label: string;
    expr: number;
  }

  const visible = (info: ExprInfo) => !['wait', 'noforward', 'other', 'l2'].includes(info.unit);

  function addrLabel(loc: string, addr: number | null): string {
    if (addr === null) return '';
    if (loc === 't') return `cycle ${addr}`;
    if (loc === 'l1bm_src' || loc === 'l1bm') return `[${addr}]`;
    if (loc === 'matx' || loc === 'maty') return `物理行 ${addr}`;
    if (loc === 'omr') return `#${addr}`;
    return `[${addr}]`;
  }

  /** Groups accesses into blocks of rows (one row per address), stacked from y0. */
  function blocks(acc: Access[], order: string[], y0: number, extra: (k: string) => string): Block[] {
    const byLoc = new Map<string, Access[]>();
    for (const a of acc) {
      const k = a.loc;
      if (!byLoc.has(k)) byLoc.set(k, []);
      byLoc.get(k)!.push(a);
    }
    const out: Block[] = [];
    let y = y0;
    const keys = [...byLoc.keys()].sort((a, b) => (order.indexOf(a) + 99 * +(order.indexOf(a) < 0)) - (order.indexOf(b) + 99 * +(order.indexOf(b) < 0)));
    for (const k of keys) {
      const list = byLoc.get(k)!;
      const rowsBy = new Map<string, Access[]>();
      for (const a of list) {
        const rk = `${a.addr}`;
        if (!rowsBy.has(rk)) rowsBy.set(rk, []);
        rowsBy.get(rk)!.push(a);
      }
      const rows: Row[] = [...rowsBy.entries()]
        .sort((a, b) => (a[1][0].addr ?? -1) - (b[1][0].addr ?? -1))
        .map(([rk, as], i) => ({ key: `${k}:${rk}`, addr: as[0].addr, label: addrLabel(k, as[0].addr), accesses: as, y: y + HEAD_H + i * ROW_H }));
      const h = HEAD_H + rows.length * ROW_H + 4;
      out.push({ key: k, title: extra(k), rows, y, h });
      y += h + GAP;
    }
    return out;
  }

  const layout = $derived.by(() => {
    if (!line) return null;
    const mine = line.accesses.filter((a) => {
      const info = line.exprs[a.expr];
      if (!info || !visible(info)) return false;
      if (a.loc === 'l1bm') return a.unit === l1b; // block writes of this PE's L1B
      if (a.loc === 'matx' || a.loc === 'maty') return a.unit === mab;
      return a.unit === pe;
    });
    const reads = mine.filter((a) => !a.write);
    const outs = mine.filter((a) => a.loc === 'out');
    const writes = mine.filter((a) => a.write && a.loc !== 'out');

    const srcBlocks = blocks(reads, ['grf0', 'grf1', 't', 'lm0', 'lm1', 'aluf', 'mauf', 'mreadf', 'lbf', 'l1bm_src'], 8, (k) => MEM_NAME[k] ?? k);
    // Matrix register as a source of matrix-vector products and transposed reads.
    let y = srcBlocks.length ? srcBlocks[srcBlocks.length - 1].y + srcBlocks[srcBlocks.length - 1].h + GAP : 8;
    const usesMatrix = line.exprs.some((e) => e.unit === 'matrix' || e.unit === 'mread');
    const matBlock = usesMatrix ? { y, h: HEAD_H + 16 * 5 + 10 } : null;

    // Expression boxes.
    const units: UnitBox[] = [];
    let uy = 8;
    line.exprs.forEach((info, i) => {
      if (!visible(info)) return;
      const nIn = Math.max(1, info.srcs.length);
      const h = HEAD_H + nIn * 22 + 30;
      const pins = info.srcs.map((s, k) => ({ label: s, y: uy + HEAD_H + 8 + k * 22 }));
      units.push({ expr: i, info, y: uy, h, pins, outY: uy + h - 16, outs: outs.filter((o) => o.expr === i) });
      uy += h + GAP;
    });

    // Destinations: memory writes, and the forwarding registers this step updates.
    const fwdWrites: Access[] = [];
    for (const u of units) {
      if (!u.info.fwd) continue;
      for (const o of u.outs) fwdWrites.push({ ...o, loc: u.info.fwd as Access['loc'], addr: null });
    }
    const dstBlocks = blocks([...writes, ...fwdWrites], ['grf0', 'grf1', 't', 'lm0', 'lm1', 'omr', 'matx', 'maty', 'l1bm', 'aluf', 'mauf', 'mreadf', 'lbf'], 8, (k) => {
      const names: Record<string, string> = {
        aluf: '$aluf（次のステップで読める）',
        mauf: '$mauf（次のステップで読める）',
        mreadf: '$mreadf（次のステップで読める）',
        lbf: '$lbf（次のステップで読める）',
        matx: '行列レジスタ $x',
        maty: '行列レジスタ $y',
        l1bm: `L1BM（L1B ${l1b}）`,
        omr: 'マスクレジスタ',
      };
      return names[k] ?? MEM_NAME[k] ?? k;
    });

    // Wires.
    const wires: Wire[] = [];
    const curve = (x1: number, y1: number, x2: number, y2: number) => {
      const mx = (x1 + x2) / 2;
      return `M${x1},${y1} C${mx},${y1} ${mx},${y2} ${x2},${y2}`;
    };
    for (const b of srcBlocks) {
      for (const r of b.rows) {
        for (const a of r.accesses) {
          const u = units.find((u) => u.expr === a.expr);
          if (!u) continue;
          const pin = u.pins[a.slot ?? 0] ?? u.pins[0];
          const py = pin ? pin.y : u.y + HEAD_H + 8;
          wires.push({ d: curve(SRC_X + SRC_W, r.y + ROW_H / 2, UNIT_X, py), kind: 'read', cycle: a.cycle, label: valueText(a), expr: a.expr });
        }
      }
    }
    if (matBlock) {
      for (const u of units.filter((u) => u.info.unit === 'matrix' || u.info.unit === 'mread')) {
        const mp = u.pins.findIndex((p) => /^\$l+[xy]/.test(p.label));
        const py = mp >= 0 ? u.pins[mp].y : u.y + HEAD_H + 8;
        for (let c = 0; c < 4; c++) wires.push({ d: curve(SRC_X + SRC_W, matBlock.y + HEAD_H, UNIT_X, py), kind: 'read', cycle: c, label: '', expr: u.expr });
      }
    }
    for (const b of dstBlocks) {
      for (const r of b.rows) {
        for (const a of r.accesses) {
          const u = units.find((u) => u.expr === a.expr);
          if (!u) continue;
          wires.push({ d: curve(UNIT_X + UNIT_W, u.outY, DST_X, r.y + ROW_H / 2), kind: 'write', cycle: a.cycle, label: valueText(a), expr: a.expr });
        }
      }
    }
    const lastSrc = matBlock ? matBlock.y + matBlock.h : srcBlocks.length ? srcBlocks[srcBlocks.length - 1].y + srcBlocks[srcBlocks.length - 1].h : 0;
    const lastDst = dstBlocks.length ? dstBlocks[dstBlocks.length - 1].y + dstBlocks[dstBlocks.length - 1].h : 0;
    const height = Math.max(160, lastSrc, uy, lastDst) + 8;
    return { srcBlocks, matBlock, units, dstBlocks, wires, height };
  });

  function valueText(a: Access): string {
    const words = a.loc === 't' || a.loc === 'out' || a.loc.endsWith('f') ? a.words.slice(0, 2) : a.words;
    if (app.view === 'f64') return format(words.slice(0, 2), 'f64').join(' ');
    return format(words, app.view).join(', ');
  }

  function rowValue(r: Row): string {
    const a = (cycle !== null ? r.accesses.find((x) => x.cycle === cycle) : undefined) ?? r.accesses[0];
    return valueText(a);
  }

  const active = (c: number) => cycle === null || c === cycle;

  /** Names of an expression's inputs, as in the SDM's descriptions. */
  function pinNames(info: ExprInfo): string[] {
    const op = info.opcode;
    switch (info.unit) {
      case 'alu':
        return op.startsWith('imm') ? ['即値'] : ['x', 'y'];
      case 'mau':
        if (op.includes('fma')) return ['a', 'b', 'c（加算）'];
        if (op.includes('mul')) return ['a', 'b'];
        if (op.includes('add')) return ['a', 'c'];
        return ['a'];
      case 'matrix':
        return op.includes('fma') ? ['行列', 'x（BF）', 'y（加算）'] : ['行列', 'x（BF）'];
      case 'mwrite':
        return ['行'];
      case 'mread':
        return ['行列'];
      case 'l1-to-pe':
        return ['L1BM'];
      case 'pe-to-l1':
        return ['PE'];
      default:
        return [];
    }
  }

  /** Color of a matrix register word: hue by sign, lightness by exponent. */
  function heat(v: number | undefined): string {
    if (v === undefined || v === 0) return 'var(--bg)';
    const exp = (v >>> 23) & 0xff;
    const t = Math.min(1, Math.abs(exp - 127) / 40);
    return `hsl(${v >>> 31 ? 210 : 25} 70% ${70 - t * 35}%)`;
  }

  /** Progress of a cycle's pulse along its wire (0 to 1), from the global step progress. */
  function pulse(w: Wire): number {
    const start = w.cycle / 4 + (w.kind === 'write' ? 0.1 : 0);
    const p = (player.progress - start) / 0.12;
    return Math.max(0, Math.min(1, p));
  }
</script>

<section class="dp">
  <header>
    <div class="tabs">
      {#each pes as p, i}
        <button class:on={i === peIdx} onclick={() => (peIdx = i)}>PE{p % 4}</button>
      {/each}
    </div>
    <span class="where">MAB #{mab}（L1B {l1b}）の PE #{pe}・{line?.lineno}行目</span>
    <div class="cycles">
      サイクル
      <button class:on={cycle === null} onclick={() => { player.pause(); player.progress = 1; pinned = null; }}>全</button>
      {#each [0, 1, 2, 3] as c}
        <button class:on={cycle === c} onclick={() => { player.setCycle(c); pinned = c; }}>{c}</button>
      {/each}
    </div>
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
  </header>
  <div class="canvas">
    {#if layout && line}
      <svg viewBox="0 0 {W} {layout.height}" width="100%" style:min-width="760px" preserveAspectRatio="xMidYMin meet">
        <text class="colhead" x={SRC_X} y="4">読み出し元（このステップの前の値）</text>
        <text class="colhead" x={UNIT_X} y="4">演算器</text>
        <text class="colhead" x={DST_X} y="4">書き込み先（このステップの後の値）</text>

        {#each layout.wires as w}
          <path class="wire {w.kind}" class:dim={!active(w.cycle)} d={w.d} />
        {/each}
        {#each layout.wires as w}
          {#if active(w.cycle) && player.progress < 1}
            <path class="pulse {w.kind}" d={w.d} pathLength="1" style:stroke-dashoffset={0.08 - pulse(w) * 1.08} />
          {/if}
        {/each}

        {#each layout.srcBlocks as b (b.key)}
          <g class="block src">
            <rect x={SRC_X} y={b.y} width={SRC_W} height={b.h} rx="5" />
            <text class="btitle" x={SRC_X + 8} y={b.y + 15}>{b.title}</text>
            {#each b.rows as r (r.key)}
              {@const on = r.accesses.some((a) => active(a.cycle))}
              <g class:dim={!on}>
                <text class="addr" x={SRC_X + 8} y={r.y + 14}>{r.label}</text>
                <text class="val" x={SRC_X + 84} y={r.y + 14}>{rowValue(r)}</text>
                <text class="cyc" x={SRC_X + SRC_W - 6} y={r.y + 14}>{r.accesses.map((a) => `c${a.cycle}`).join(' ')}</text>
              </g>
            {/each}
          </g>
        {/each}
        {#if layout.matBlock}
          <g class="block src">
            <rect x={SRC_X} y={layout.matBlock.y} width={SRC_W} height={layout.matBlock.h} rx="5" />
            <text class="btitle" x={SRC_X + 8} y={layout.matBlock.y + 15}>行列レジスタ（MAB の4 PE で共有）</text>
            {#each ['matx', 'maty'] as side, si}
              <text class="addr" x={SRC_X + 8 + si * 150} y={layout.matBlock.y + HEAD_H + 10}>${side === 'matx' ? 'x' : 'y'}</text>
              {#each Array(16) as _, row}
                {#each Array(8) as _, w}
                  {@const v = read(app.before, `mab:${mab}`, side, row * 8 + w)}
                  <rect x={SRC_X + 24 + si * 150 + w * 15} y={layout.matBlock.y + HEAD_H + row * 5} width="14" height="4" style:fill={heat(v)}>
                    <title>{side} 物理行 {row} 語 {w}: {v === undefined ? '0' : format([v], app.view)[0]}</title>
                  </rect>
                {/each}
              {/each}
            {/each}
          </g>
        {/if}

        {#each layout.units as u (u.expr)}
          <g class="unit {u.info.unit}">
            <rect x={UNIT_X} y={u.y} width={UNIT_W} height={u.h} rx="6" />
            <text class="btitle" x={UNIT_X + 8} y={u.y + 15}>{UNIT_NAME[u.info.unit] ?? u.info.unit}：<tspan class="op">{u.info.opcode}</tspan></text>
            {#each u.pins as p, k}
              <circle class="pin" cx={UNIT_X} cy={p.y} r="3.5" />
              <text class="pinlabel" x={UNIT_X + 8} y={p.y + 4}>{pinNames(u.info)[k] ?? k} ← {p.label}</text>
            {/each}
            <circle class="pin out" cx={UNIT_X + UNIT_W} cy={u.outY} r="3.5" />
            <text class="pinlabel" x={UNIT_X + UNIT_W - 8} y={u.outY + 4} text-anchor="end">→ {u.info.dsts.join(' ')}</text>
            {#if u.outs.length}
              {@const o = u.outs.find((x) => cycle === null || x.cycle === cycle) ?? u.outs[0]}
              <text class="outval" x={UNIT_X + 8} y={u.outY - 10}>結果 c{o.cycle}: {valueText(o)}</text>
            {/if}
          </g>
        {/each}

        {#each layout.dstBlocks as b (b.key)}
          <g class="block dst">
            <rect x={DST_X} y={b.y} width={DST_W} height={b.h} rx="5" />
            <text class="btitle" x={DST_X + 8} y={b.y + 15}>{b.title}</text>
            {#each b.rows as r (r.key)}
              {@const on = r.accesses.some((a) => active(a.cycle))}
              <g class:dim={!on}>
                <text class="addr" x={DST_X + 8} y={r.y + 14}>{r.label}</text>
                <text class="val" x={DST_X + 84} y={r.y + 14}>{rowValue(r)}</text>
                <text class="cyc" x={DST_X + DST_W - 6} y={r.y + 14}>{r.accesses.map((a) => `c${a.cycle}`).join(' ')}</text>
              </g>
            {/each}
          </g>
        {/each}
      </svg>
      {#if line.kind !== 'pe'}
        <p class="note">{line.kind === 'nop' ? 'nop：このステップでは PE は何もしない（フォワーディングレジスタも更新されない）。' : line.kind === 'mv' ? 'MV 命令：PE の外（DRAM / PDM / L2BM）での転送。上のチップ図を見てください。' : ''}</p>
      {:else if layout.units.length === 0}
        <p class="note">この行の式は、この PE のデータパスを使いません（L2BM ↔ L1BM の転送などは上のチップ図）。</p>
      {/if}
    {/if}
  </div>
</section>

<style>
  .dp {
    display: flex;
    flex-direction: column;
    min-height: 0;
    min-width: 0;
  }
  header {
    display: flex;
    align-items: center;
    gap: 14px;
    padding: 4px 8px;
    font-size: 12px;
    flex-wrap: wrap;
  }
  .where {
    color: var(--muted);
    margin-right: auto;
  }
  .tabs,
  .cycles {
    display: flex;
    gap: 3px;
    align-items: center;
  }
  button.on {
    background: var(--accent);
    color: var(--bg);
  }
  .canvas {
    flex: 1;
    min-height: 0;
    overflow: auto;
    padding: 4px 8px;
  }
  svg {
    overflow: visible;
  }
  text {
    font-size: 11px;
    fill: var(--fg);
  }
  .colhead {
    font-size: 10px;
    fill: var(--muted);
  }
  .block rect {
    fill: var(--panel);
    stroke: var(--line);
  }
  .block.src rect {
    stroke: color-mix(in srgb, var(--c-l2) 60%, var(--line));
  }
  .block.dst rect {
    stroke: color-mix(in srgb, var(--c-compute) 60%, var(--line));
  }
  .btitle {
    font-weight: 600;
    font-size: 11px;
  }
  .op {
    font-family: var(--mono);
  }
  .addr,
  .val,
  .cyc,
  .pinlabel,
  .outval {
    font-family: var(--mono);
  }
  .addr {
    fill: var(--muted);
  }
  .cyc {
    text-anchor: end;
    fill: var(--muted);
    font-size: 9px;
  }
  .dim {
    opacity: 0.25;
  }
  .unit rect {
    fill: color-mix(in srgb, var(--c-compute) 10%, var(--panel));
    stroke: var(--line);
  }
  .unit.mau rect,
  .unit.matrix rect,
  .unit.mwrite rect,
  .unit.mread rect {
    fill: color-mix(in srgb, var(--c-mau) 10%, var(--panel));
  }
  .unit.l1-to-pe rect,
  .unit.pe-to-l1 rect {
    fill: color-mix(in srgb, var(--c-l1) 12%, var(--panel));
  }
  .pin {
    fill: var(--bg);
    stroke: var(--fg);
  }
  .pinlabel {
    font-size: 10px;
  }
  .outval {
    font-size: 10px;
    fill: var(--accent);
  }
  .wire {
    fill: none;
    stroke-width: 1.6;
  }
  .wire.read {
    stroke: var(--c-l2);
  }
  .wire.write {
    stroke: var(--c-compute);
  }
  .wire.dim {
    opacity: 0.15;
  }
  .pulse {
    fill: none;
    stroke-width: 4;
    stroke-dasharray: 0.08 1;
    stroke-linecap: round;
  }
  .pulse.read {
    stroke: var(--c-l2);
  }
  .pulse.write {
    stroke: var(--c-compute);
  }
  .note {
    color: var(--muted);
    font-size: 12px;
  }
</style>
