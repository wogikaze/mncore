<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { player } from '../lib/player.svelte';
  import { CATEGORY_COLORS, category } from '../lib/flows';
  import { volume } from '../lib/numbers';
  import type { Flow, Region } from '../lib/types';

  // Memory map of the chip: each memory is a bar over the addresses the program uses; the
  // current line's source regions are blue, destinations orange, linked by curves.
  const W = 1000;
  const LEFT = 64;
  const GROUP_W = (W - LEFT - 8) / 4;
  const BAR_W = GROUP_W / 2 - 12;
  const Y = { dram: 18, pdm: 46, l2bm: 94, l1bm: 132, pe: 206 };
  const L1_H = 6;
  const PE_H = 30;
  const H = Y.pe + PE_H + 22;

  type Bar = { x: number; y: number; w: number; h: number };

  function bar(mem: Region['mem'] | 'pe', unit: number): Bar {
    switch (mem) {
      case 'dram':
        return { x: LEFT + unit * GROUP_W + 4, y: Y.dram, w: BAR_W, h: 16 };
      case 'pdm':
        return { x: LEFT + unit * GROUP_W + 4, y: Y.pdm, w: BAR_W, h: 16 };
      case 'l2bm': {
        const g = Math.floor(unit / 2);
        return { x: LEFT + g * GROUP_W + 4 + (unit % 2) * (BAR_W + 12), y: Y.l2bm, w: BAR_W, h: 16 };
      }
      case 'l1bm': {
        const p = bar('l2bm', Math.floor(unit / 8));
        return { x: p.x, y: Y.l1bm + (unit % 8) * (L1_H + 2), w: BAR_W, h: L1_H };
      }
      case 'pe': {
        const p = bar('l2bm', Math.floor(unit / 8));
        const w = BAR_W / 8;
        return { x: p.x + (unit % 8) * w, y: Y.pe, w: w - 1, h: PE_H };
      }
    }
  }

  const trace = $derived(app.trace);
  const flows = $derived<Flow[]>(trace?.lines[app.line]?.flows ?? []);

  /** Address extent of each memory kind over the whole program (the bars' scale). */
  const extent = $derived.by(() => {
    const e: Record<string, number> = { dram: 64, pdm: 64, l2bm: 64, l1bm: 64 };
    for (const l of trace?.lines ?? []) {
      for (const f of l.flows) {
        for (const r of [f.src, f.dst]) if (r) e[r.mem] = Math.max(e[r.mem], r.addr + r.len);
      }
    }
    return e;
  });

  /** Part of a bar covered by a region. */
  function span(r: Region, unit: number): Bar {
    const b = bar(r.mem, unit);
    const ext = extent[r.mem];
    const x = b.x + (r.addr / ext) * b.w;
    const w = Math.max(2, (Math.min(r.len, ext - r.addr) / ext) * b.w);
    return { x, y: b.y, w, h: b.h };
  }

  function curve(a: Bar, b: Bar): string {
    const x1 = a.x + a.w / 2;
    const x2 = b.x + b.w / 2;
    const down = b.y > a.y;
    const y1 = down ? a.y + a.h : a.y;
    const y2 = down ? b.y : b.y + b.h;
    const my = (y1 + y2) / 2;
    return `M${x1},${y1} C${x1},${my} ${x2},${my} ${x2},${y2}`;
  }

  const drawn = $derived.by(() => {
    const regions: { b: Bar; kind: 'src' | 'dst' }[] = [];
    const links: { d: string; color: string }[] = [];
    let compute = false;
    const peUnits = new Set<number>();
    for (const f of flows) {
      const color = CATEGORY_COLORS[category(f.from, f.to)];
      if (!f.src && !f.dst) {
        compute = true;
        continue;
      }
      const srcBars = f.src ? f.src.units.map((u) => span(f.src!, u)) : [];
      const dstBars = f.dst ? f.dst.units.map((u) => span(f.dst!, u)) : [];
      if (f.from === 'pe' || f.to === 'pe') {
        // PE side of L1BM transfers: the L1B's column of the PE band.
        const r = (f.src ?? f.dst)!;
        for (const u of r.units) peUnits.add(u);
        const pes = r.units.map((u) => bar('pe', u));
        if (f.to === 'pe') pes.forEach((p, i) => links.push({ d: curve(srcBars[i], p), color }));
        else pes.forEach((p, i) => links.push({ d: curve(p, dstBars[i]), color }));
      } else if (srcBars.length && dstBars.length) {
        const ns = srcBars.length;
        const nd = dstBars.length;
        if (nd >= ns) dstBars.forEach((d, i) => links.push({ d: curve(srcBars[Math.floor((i * ns) / nd)], d), color }));
        else srcBars.forEach((s, i) => links.push({ d: curve(s, dstBars[Math.floor((i * nd) / ns)]), color }));
      }
      srcBars.forEach((b) => regions.push({ b, kind: 'src' }));
      dstBars.forEach((b) => regions.push({ b, kind: 'dst' }));
    }
    return { regions, links, compute, peUnits };
  });

  const focusL1b = $derived(Math.floor(app.focusPe / 64));
  const focusMab = $derived(Math.floor(app.focusPe / 4) % 16);
  const pulse = $derived(player.progress < 1 ? player.progress : -1);

  const FULL: Record<string, number> = { dram: 4, pdm: 4, l2bm: 8, l1bm: 64 };
  function describe(r: Region | null): string {
    if (!r) return 'PE';
    const name = (u: number) => (r.mem === 'l2bm' ? `${Math.floor(u / 2)}.${u % 2}` : r.mem === 'l1bm' ? `${u}` : `g${u}`);
    const us = r.units.length === FULL[r.mem] ? '全' : r.units.length > 4 ? `${r.units.length}個` : r.units.map(name).join(',');
    return `${r.mem.toUpperCase()} ${us} [${r.addr}..${r.addr + r.len - 1}]`;
  }

  const COMPUTE_NAME: Record<string, string> = { alu: 'ALU 演算', mau: 'MAU ベクトル演算', matrix: '行列演算' };
  const LEVELS: [string, number][] = [
    ['DRAM', Y.dram],
    ['PDM', Y.pdm],
    ['L2BM', Y.l2bm],
    ['L1BM', Y.l1bm],
    ['PE', Y.pe],
  ];
</script>

<section class="chip">
  <svg viewBox="0 0 {W} {H}" preserveAspectRatio="xMidYMin meet">
    {#each LEVELS as [name, y]}
      <text class="lvl" x="6" y={y + 12}>{name}</text>
    {/each}
    {#each [0, 1, 2, 3] as g}
      {@const d = bar('dram', g)}
      {@const p = bar('pdm', g)}
      <text class="glabel" x={LEFT + g * GROUP_W + 4} y="12">group {g}</text>
      <rect class="bar dram" x={d.x} y={d.y} width={d.w} height={d.h} />
      <rect class="bar pdm" x={p.x} y={p.y} width={p.w} height={p.h} />
    {/each}
    {#each Array(8) as _, u}
      {@const b = bar('l2bm', u)}
      <rect class="bar l2" x={b.x} y={b.y} width={b.w} height={b.h} />
      <text class="unitlabel" x={b.x + b.w / 2} y={b.y + 12}>{Math.floor(u / 2)}.{u % 2}</text>
    {/each}
    {#each Array(64) as _, u}
      {@const b = bar('l1bm', u)}
      {@const pb = bar('pe', u)}
      <rect class="bar l1" class:focus={u === focusL1b} x={b.x} y={b.y} width={b.w} height={b.h}><title>L1BM {u}</title></rect>
      <rect class="pe" class:focus={u === focusL1b} class:hot={drawn.compute || drawn.peUnits.has(u)} x={pb.x} y={pb.y} width={pb.w} height={pb.h}><title>L1B {u} の 64 PE</title></rect>
    {/each}
    <rect class="mabmark" x={bar('pe', focusL1b).x - 1} y={Y.pe + (focusMab * PE_H) / 16} width={bar('pe', focusL1b).w + 2} height={PE_H / 16 + 1} />

    {#each drawn.links as l}
      <path class="link" d={l.d} style:stroke={l.color} />
      {#if pulse >= 0}
        <path class="pulse" d={l.d} pathLength="1" style:stroke={l.color} style:stroke-dashoffset={0.1 - pulse * 1.1} />
      {/if}
    {/each}
    {#each drawn.regions as r}
      <rect class="region {r.kind}" x={r.b.x} y={r.b.y} width={r.b.w} height={r.b.h} />
    {/each}
    <text class="scale" x={W - 8} y={H - 6}>帯の長さ = プログラムで使うアドレス範囲（DRAM {extent.dram}・PDM {extent.pdm}・L2BM {extent.l2bm}・L1BM {extent.l1bm} 長語）。青 = 読む範囲、橙 = 書く範囲</text>
  </svg>
  <ul class="flows">
    {#each flows as f}
      <li style:border-color={CATEGORY_COLORS[category(f.from, f.to)]}>
        {#if f.src || f.dst}
          <b>{describe(f.src)}</b> → <b>{describe(f.dst)}</b>
        {:else}
          PE 内の{f.from === 'matrix' ? '行列レジスタ読み出し' : (COMPUTE_NAME[f.to] ?? f.to)}
        {/if}
        <span class="kind">{f.kind}・{volume(f.longs)}</span>
      </li>
    {:else}
      <li class="none">この行には転送も演算もありません</li>
    {/each}
  </ul>
</section>

<style>
  .chip {
    display: flex;
    flex-direction: column;
    min-height: 0;
    min-width: 0;
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
  .lvl,
  .glabel,
  .scale {
    fill: var(--muted);
  }
  .scale {
    text-anchor: end;
    font-size: 9px;
  }
  .unitlabel {
    text-anchor: middle;
    font-size: 9px;
    fill: var(--muted);
  }
  .bar {
    stroke: var(--line);
    stroke-width: 0.5;
  }
  .dram,
  .pdm {
    fill: color-mix(in srgb, var(--c-offchip) 10%, var(--panel));
  }
  .l2 {
    fill: color-mix(in srgb, var(--c-l2) 10%, var(--panel));
  }
  .l1 {
    fill: color-mix(in srgb, var(--c-l1) 12%, var(--panel));
  }
  .pe {
    fill: color-mix(in srgb, var(--c-compute) 8%, var(--panel));
  }
  .pe.hot {
    fill: color-mix(in srgb, var(--c-compute) 40%, var(--panel));
  }
  .focus {
    stroke: var(--fg);
    stroke-width: 1;
  }
  .mabmark {
    fill: var(--fg);
  }
  .region.src {
    fill: var(--c-l2);
  }
  .region.dst {
    fill: var(--c-compute);
  }
  .link {
    fill: none;
    stroke-width: 1;
    opacity: 0.55;
  }
  .pulse {
    fill: none;
    stroke-width: 3;
    stroke-dasharray: 0.1 1;
    stroke-linecap: round;
  }
  .flows {
    list-style: none;
    margin: 0;
    padding: 4px 8px;
    display: flex;
    flex-wrap: wrap;
    gap: 4px 10px;
    font-size: 11px;
  }
  .flows li {
    border-left: 3px solid;
    padding-left: 6px;
  }
  .flows b {
    font-family: var(--mono);
    font-weight: 500;
  }
  .kind {
    color: var(--muted);
    margin-left: 6px;
  }
  .flows .none {
    border: none;
    color: var(--muted);
  }
</style>
