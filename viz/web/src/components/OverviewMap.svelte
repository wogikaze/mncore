<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { player } from '../lib/player.svelte';
  import { CATEGORY_COLORS } from '../lib/flows';
  import { activityOf, groupOfMab, l1bOfMab, l2bOfMab } from '../lib/hierarchy';

  let { large = false, onfull, onclose }: { large?: boolean; onfull?: () => void; onclose?: () => void } = $props();

  // Position map only. The compact version is for orientation; the large version is the
  // full-chip mode and shows the 16 MAB dots and L1B labels.
  const W = 900;
  const GW = 430;
  const GH = $derived(large ? 196 : 108);
  const GAP = 10;
  const M = 6;

  const GROUP_CELL: Record<number, [number, number]> = { 0: [0, 0], 1: [1, 0], 2: [1, 1], 3: [0, 1] };

  const trace = $derived(app.trace);
  const line = $derived(trace?.lines[app.line]);
  const act = $derived(activityOf(line?.flows ?? []));
  const focusGroup = $derived(groupOfMab(app.focusMab));
  const focusL2b = $derived(l2bOfMab(app.focusMab));
  const focusL1b = $derived(l1bOfMab(app.focusMab));
  const focusMab = $derived(app.focusMab);
  const pulse = $derived(player.progress < 1 ? player.progress : -1);

  interface Box {
    x: number;
    y: number;
    w: number;
    h: number;
  }

  function groupXY(g: number) {
    const [c, r] = GROUP_CELL[g];
    return { x: M + c * (GW + GAP), y: M + r * (GH + GAP) };
  }

  function groupParts(g: number) {
    const { x, y } = groupXY(g);
    const top = g < 2;
    const de: Box = { x: x + 66, y: y + (top ? 18 : GH - 30), w: 298, h: large ? 18 : 10 };
    const dram: Box = { x: x + 124, y: y + (top ? 4 : GH - 12), w: 180, h: large ? 10 : 7 };
    const pdm: Box = { x: x + 6, y: y + (top ? 18 : GH - 46), w: 30, h: large ? 40 : 28 };
    const y0 = top ? 40 : 8;
    const l2bs: Box[] = [0, 1].map((i) => ({ x: x + 6 + i * 212, y: y + y0, w: 204, h: large ? 148 : 64 }));
    return { x, y, top, dram, de, pdm, l2bs };
  }

  function tileBox(g: number, l2bInGroup: number, i: number): Box {
    const b = groupParts(g).l2bs[l2bInGroup];
    if (large) {
      return { x: b.x + 5 + (i % 4) * 49, y: b.y + 26 + Math.floor(i / 4) * 46, w: 46, h: 42 };
    }
    return { x: b.x + 5 + (i % 4) * 48, y: b.y + 18 + Math.floor(i / 4) * 24, w: 45, h: 21 };
  }

  function colorOf(c: string | undefined) {
    return c ? CATEGORY_COLORS[c] : undefined;
  }

  function selectGroup(g: number) {
    app.selectGroup(g);
  }

  function selectL1b(l1b: number) {
    app.selectL1b(l1b);
  }

  function center(b: Box) {
    return { x: b.x + b.w / 2, y: b.y + b.h / 2 };
  }

  function seg(a: { x: number; y: number }, b: { x: number; y: number }) {
    return `M${a.x},${a.y} L${b.x},${b.y}`;
  }

  function offchipPaths(g: number): string[] {
    const p = groupParts(g);
    const de = center(p.de);
    const dram = center(p.dram);
    const pdm = center(p.pdm);
    return [
      seg(
        { x: dram.x, y: p.top ? p.dram.y + p.dram.h : p.dram.y },
        { x: de.x, y: p.top ? p.de.y : p.de.y + p.de.h },
      ),
      seg({ x: p.pdm.x + p.pdm.w, y: pdm.y }, { x: p.de.x, y: de.y }),
    ];
  }

  function l2bPath(l2b: number): string {
    const g = Math.floor(l2b / 2);
    const p = groupParts(g);
    const b = p.l2bs[l2b % 2];
    const de = center(p.de);
    const l = center(b);
    return seg(
      { x: de.x, y: p.top ? p.de.y + p.de.h : p.de.y },
      { x: l.x, y: p.top ? b.y : b.y + b.h },
    );
  }

  function l1bPath(t: { box: Box }): string {
    const c = center(t.box);
    return seg({ x: c.x, y: t.box.y }, { x: c.x, y: c.y });
  }

  function onKey(ev: KeyboardEvent, fn: () => void) {
    if (ev.key === 'Enter' || ev.key === ' ') {
      ev.preventDefault();
      fn();
    }
  }

  const l1bTiles = $derived.by(() =>
    Array.from({ length: 64 }, (_, l1b) => {
      const g = Math.floor(l1b / 16);
      const l2b = Math.floor(l1b / 8);
      const i = l1b % 8;
      return { l1b, g, l2b, box: tileBox(g, l2b % 2, i) };
    }),
  );

</script>

<section class="overview" class:large>
  <header>
    <span class="title">チップ全体</span>
    <span class="path">G{focusGroup} / L2B {focusL2b} / L1B {focusL1b}</span>
    {#if !large && onfull}
      <button onclick={onfull}>全体表示</button>
    {:else if large && onclose}
      <button onclick={onclose}>詳細に戻る</button>
    {/if}
    <span class="hwlegend">
      <i class="proc"></i>処理
      <i class="mem"></i>メモリ
      <i class="layer"></i>Layer
    </span>
    <span class="legend">
      <i style:background={CATEGORY_COLORS.offchip}></i>DRAM/PDM
      <i style:background={CATEGORY_COLORS.l2}></i>L2BM
      <i style:background={CATEGORY_COLORS.l1}></i>L1BM
      <i style:background={CATEGORY_COLORS.compute}></i>PE
    </span>
  </header>

  <svg viewBox="0 0 {W} {large ? 420 : 240}" preserveAspectRatio="xMidYMin meet">
    <defs>
      {#each Object.entries(CATEGORY_COLORS) as [id, color]}
        <marker id={`ov-arrow-${id}`} viewBox="0 0 8 8" refX="7" refY="4" markerWidth="5" markerHeight="5" orient="auto">
          <path d="M0,0 L8,4 L0,8 z" fill={color} />
        </marker>
      {/each}
    </defs>
    {#each [0, 1, 2, 3] as g}
      {@const p = groupParts(g)}
      {@const gc = colorOf(act.groups.get(g))}
      <g class="group" class:active={Boolean(gc)} class:selected={app.scope === 'group' && focusGroup === g}>
        <rect class="gbox" x={p.x} y={p.y} width={GW} height={GH} rx="4" style:stroke={gc ?? undefined} />
        <text class="glabel click" x={p.x + 6} y={p.top ? p.y + 12 : p.y + GH - 3} role="button" tabindex="0" onclick={() => selectGroup(g)} onkeydown={(e) => onKey(e, () => selectGroup(g))}>Group {g}</text>
        <rect class="dram" x={p.dram.x} y={p.dram.y} width={p.dram.w} height={p.dram.h} rx="1" />
        <rect class="pdm" x={p.pdm.x} y={p.pdm.y} width={p.pdm.w} height={p.pdm.h} rx="1" />
        <rect class="de" x={p.de.x} y={p.de.y} width={p.de.w} height={p.de.h} rx="1" />
        {#if large}
          <text class="micro" x={p.dram.x + p.dram.w / 2} y={p.dram.y + p.dram.h - 2}>DRAM I/F</text>
          <text class="micro" x={p.pdm.x + p.pdm.w / 2} y={p.pdm.y + 12}>PDM</text>
          <text class="micro" x={p.de.x + p.de.w / 2} y={p.de.y + p.de.h / 2 + 3}>Data Engine</text>
        {/if}

        {#each [0, 1] as i}
          {@const b = p.l2bs[i]}
          {@const l2b = g * 2 + i}
          {@const lc = colorOf(act.l2bs.get(l2b))}
          <g class="l2b" class:active={Boolean(lc)} role="button" tabindex="0" onclick={() => selectL1b(l2b * 8)} onkeydown={(e) => onKey(e, () => selectL1b(l2b * 8))}>
            <rect x={b.x} y={b.y} width={b.w} height={b.h} rx="2" style:stroke={lc ?? undefined} />
            <text class="l2label" x={b.x + 4} y={b.y + 9}>L2B {l2b}</text>
            <rect class="l2bm" x={b.x + 4} y={b.y + 12} width={b.w - 8} height="3" rx="1" />
          </g>
        {/each}

        {#each l1bTiles.filter((t) => t.g === g) as t (t.l1b)}
          {@const c = colorOf(act.l1bs.get(t.l1b))}
          {@const selected = app.scope !== 'group' && focusL1b === t.l1b}
          {@const current = focusL1b === t.l1b}
          <g
            class="tile"
            class:active={Boolean(c)}
            class:selected
            class:current
            role="button"
            tabindex="0"
            onclick={() => selectL1b(t.l1b)}
            onkeydown={(e) => onKey(e, () => selectL1b(t.l1b))}
          >
            <title>Group {t.g} / L2B {t.l2b} / L1B {t.l1b}</title>
            <rect x={t.box.x} y={t.box.y} width={t.box.w} height={t.box.h} rx="1" style:stroke={c ?? undefined} />
            {#if c}<rect class="tilefill" x={t.box.x} y={t.box.y} width={t.box.w} height={t.box.h} rx="1" style:fill={c} />{/if}
            {#if large}
              {#each Array(16) as _, m}
                <rect
                  class="mabdot"
                  class:focus={t.l1b * 16 + m === focusMab}
                  x={t.box.x + 3 + (m % 4) * 5}
                  y={t.box.y + 3 + Math.floor(m / 4) * 5}
                  width="3.5"
                  height="3.5"
                />
              {/each}
              <text class="l1label" x={t.box.x + 3} y={t.box.y + t.box.h - 4}>L1B {t.l1b}</text>
            {:else}
              {#each Array(16) as _, m}
                {#if t.l1b * 16 + m === focusMab}
                  <circle class="focusdot" cx={t.box.x + 6 + (m % 4) * 5} cy={t.box.y + 5 + Math.floor(m / 4) * 5} r="2.2" />
                {/if}
              {/each}
              {#if current}<text class="l1label" x={t.box.x + 30} y={t.box.y + 15}>{t.l1b}</text>{/if}
            {/if}
            {#if c && pulse >= 0 && current}
              <circle class="pulse" cx={t.box.x + t.box.w / 2} cy={t.box.y + t.box.h / 2} r={2 + pulse * 5} style:stroke={c} />
            {/if}
          </g>
        {/each}
      </g>
    {/each}
    <g class="flowpaths">
      {#each [0, 1, 2, 3] as g}
        {@const gc = act.groups.get(g)}
        {#if gc}
          {#each offchipPaths(g) as d}
            <path class="flowpath" d={d} style:stroke={CATEGORY_COLORS[gc]} marker-end={`url(#ov-arrow-${gc})`} />
          {/each}
        {/if}
        {#each [0, 1] as i}
          {@const l2b = g * 2 + i}
          {@const lc = act.l2bs.get(l2b)}
          {#if lc}
            <path class="flowpath" d={l2bPath(l2b)} style:stroke={CATEGORY_COLORS[lc]} marker-end={`url(#ov-arrow-${lc})`} />
          {/if}
        {/each}
      {/each}
      {#each l1bTiles as t (t.l1b)}
        {@const c = act.l1bs.get(t.l1b)}
        {#if c && (large || t.l1b === focusL1b)}
          <path class="flowpath" d={l1bPath(t)} style:stroke={CATEGORY_COLORS[c]} marker-end={`url(#ov-arrow-${c})`} />
        {/if}
      {/each}
    </g>
  </svg>
</section>

<style>
  .overview {
    display: flex;
    flex-direction: column;
    min-height: 0;
    min-width: 0;
    background: var(--panel);
  }
  header {
    display: flex;
    align-items: center;
    gap: 8px;
    padding: 4px 8px 0;
    font-size: 11px;
    flex-wrap: wrap;
  }
  .title {
    font-weight: 700;
    font-size: 12px;
    letter-spacing: 0.02em;
  }
  .path {
    font-family: var(--mono);
    color: var(--muted);
  }
  header button {
    font-size: 10px;
    padding: 1px 6px;
  }
  .hwlegend {
    display: flex;
    align-items: center;
    gap: 3px;
    color: var(--muted);
    font-size: 10px;
    white-space: nowrap;
  }
  .hwlegend i {
    width: 8px;
    height: 8px;
    border-radius: 2px;
    margin-left: 3px;
  }
  .hwlegend .proc {
    background: var(--hw-proc);
  }
  .hwlegend .mem {
    background: var(--hw-mem);
  }
  .hwlegend .layer {
    background: var(--hw-layer-line);
  }
  .legend {
    margin-left: auto;
    display: flex;
    align-items: center;
    gap: 3px;
    color: var(--muted);
    font-size: 10px;
    white-space: nowrap;
  }
  .legend i {
    width: 7px;
    height: 7px;
    border-radius: 2px;
    margin-left: 4px;
  }
  svg {
    width: 100%;
    flex: 1 1 0;
    min-height: 0;
    height: 0;
    display: block;
    overflow: hidden;
  }
  .gbox {
    fill: color-mix(in srgb, var(--bg) 55%, var(--panel));
    stroke: var(--line-strong);
    stroke-width: 1;
  }
  .group.active .gbox {
    fill: color-mix(in srgb, var(--accent) 5%, var(--panel));
  }
  .group.selected .gbox {
    stroke: var(--fg);
    stroke-width: 1.5;
  }
  .dram,
  .de {
    fill: var(--hw-proc);
    stroke: var(--hw-proc-line);
  }
  .pdm,
  .l2bm {
    fill: var(--hw-mem);
    stroke: var(--hw-mem-line);
  }
  .l2b > rect {
    fill: var(--hw-layer);
    stroke: var(--hw-layer-line);
  }
  .l2b.active > rect {
    stroke-width: 2;
  }
  .glabel {
    font-size: 14px;
    font-weight: 700;
    fill: var(--fg);
  }
  .l2label {
    font-size: 12px;
    fill: var(--fg);
  }
  .micro {
    font-size: 9px;
    text-anchor: middle;
    fill: var(--muted);
  }
  .tile {
    cursor: pointer;
  }
  .tile > rect:first-of-type {
    fill: color-mix(in srgb, var(--hw-layer-line) 16%, var(--panel));
    stroke: color-mix(in srgb, var(--hw-layer-line) 60%, var(--line));
    stroke-width: 0.8;
  }
  .tile.active > rect:first-of-type {
    stroke-width: 1.5;
  }
  .tile.current > rect:first-of-type {
    stroke: var(--fg);
    stroke-width: 1.5;
  }
  .tile.selected > rect:first-of-type {
    stroke: var(--accent);
    stroke-width: 2;
  }
  .tilefill {
    fill-opacity: 0.24;
    stroke: none;
  }
  .mabdot {
    fill: color-mix(in srgb, var(--fg) 35%, transparent);
  }
  .mabdot.focus {
    fill: var(--accent);
  }
  .focusdot {
    fill: var(--accent);
  }
  .l1label {
    font-size: 10px;
    font-weight: 600;
  }
  .pulse {
    fill: none;
    stroke-width: 2;
  }
  .flowpaths {
    pointer-events: none;
  }
  .flowpath {
    fill: none;
    stroke-width: 1.4;
    opacity: 0.8;
  }
  .overview.large .flowpath {
    stroke-width: 2.2;
  }
</style>
