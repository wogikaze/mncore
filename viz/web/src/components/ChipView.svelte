<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { player } from '../lib/player.svelte';
  import { CATEGORY_COLORS, CATEGORY_NAMES, category } from '../lib/flows';
  import { format, volume } from '../lib/numbers';
  import { read } from '../lib/memory';
  import type { Access, Flow, Region } from '../lib/types';

  // Hierarchical view of the machine, following the official four-group tree:
  // Group -> 2 L2B -> 8 L1B -> 16 MAB -> 4 PE. The overview shows all 64 L1B tiles;
  // opening a tile shows its 16 MAB, the shared L1BM and the focus PE values.

  const W = 1200;
  const H = 420;
  const GW = 584;
  const GH = 196;
  const GGAP = 10;
  const GM = 8;

  let level = $state<'chip' | 'l1b'>('chip');

  const trace = $derived(app.trace);
  const line = $derived(trace?.lines[app.line]);
  const flows = $derived<Flow[]>(line?.flows ?? []);
  const focusMab = $derived(app.focusMab);
  const focusL1b = $derived(Math.floor(focusMab / 16));
  const focusL2b = $derived(Math.floor(focusL1b / 8));
  const focusGroup = $derived(Math.floor(focusL1b / 16));
  const peBase = $derived(focusMab * 4);
  const focusValue = $derived(line ? peSummary(peBase + app.peIndex).outFirst : '');
  const pulse = $derived(player.progress < 1 ? player.progress : -1);

  $effect(() => {
    // A different problem starts again at the chip overview.
    app.problem;
    level = 'chip';
  });

  interface Box {
    x: number;
    y: number;
    w: number;
    h: number;
  }

  const GROUP_CELL: Record<number, [number, number]> = { 0: [0, 0], 1: [1, 0], 2: [1, 1], 3: [0, 1] };

  function groupXY(g: number) {
    const [c, r] = GROUP_CELL[g];
    return { x: GM + c * (GW + GGAP), y: GM + r * (GH + GGAP) };
  }

  /** Top groups have DRAM and Data Engine above their L2B blocks; bottom groups below. */
  function groupParts(g: number) {
    const { x, y } = groupXY(g);
    const top = g < 2;
    const dram: Box = { x: x + GW / 2 - 110, y: y + (top ? 18 : GH - 34), w: 220, h: 16 };
    const de: Box = { x: x + GW / 2 - 215, y: y + (top ? 38 : GH - 56), w: 430, h: 18 };
    const pdm: Box = { x: x + 6, y: de.y - 14, w: 38, h: 46 };
    const l2bs: Box[] = [0, 1].map((i) => ({ x: x + (i === 0 ? 50 : 332), y: y + (top ? 62 : 10), w: 232, h: 124 }));
    return { x, y, dram, de, pdm, l2bs };
  }

  interface Tile {
    l1b: number;
    group: number;
    l2b: number;
    box: Box;
  }

  const tiles = $derived.by<Tile[]>(() =>
    Array.from({ length: 64 }, (_, l1b) => {
      const group = Math.floor(l1b / 16);
      const l2b = Math.floor(l1b / 8);
      const parts = groupParts(group);
      const b = parts.l2bs[l2b % 2];
      const i = l1b % 8;
      const box = { x: b.x + 6 + (i % 4) * 56, y: b.y + 32 + Math.floor(i / 4) * 46, w: 52, h: 42 };
      return { l1b, group, l2b, box };
    }),
  );

  /** Units touched by the current line's flows, with the strongest category per unit. */
  const active = $derived.by(() => {
    const groups = new Map<number, string>();
    const l2bs = new Map<number, string>();
    const l1bs = new Map<number, string>();
    const cats = new Set<string>();
    let compute = 0;
    const rank = (c: string) => (c === 'l1' ? 3 : c === 'l2' ? 2 : c === 'offchip' ? 1 : 0);
    const put = (m: Map<number, string>, u: number, c: string) => {
      const old = m.get(u);
      if (!old || rank(c) > rank(old)) m.set(u, c);
    };
    for (const f of flows) {
      const c = category(f.from, f.to);
      cats.add(c);
      if (!f.src && !f.dst) {
        compute++;
        continue;
      }
      for (const r of [f.src, f.dst]) {
        if (!r) continue;
        if (r.mem === 'dram' || r.mem === 'pdm') {
          for (const g of r.units) put(groups, g, c);
        } else if (r.mem === 'l2bm') {
          for (const u of r.units) {
            put(l2bs, u, c);
            put(groups, Math.floor(u / 2), c);
          }
        } else if (r.mem === 'l1bm') {
          for (const u of r.units) {
            put(l1bs, u, c);
            put(l2bs, Math.floor(u / 8), c);
            put(groups, Math.floor(u / 16), c);
          }
        }
      }
    }
    return { groups, l2bs, l1bs, cats, compute };
  });

  const colorOf = (c: string | undefined) => (c ? CATEGORY_COLORS[c] : undefined);

  function center(b: Box) {
    return { x: b.x + b.w / 2, y: b.y + b.h / 2 };
  }

  function linePath(a: { x: number; y: number }, b: { x: number; y: number }): string {
    return `M${a.x},${a.y} L${b.x},${b.y}`;
  }

  function offchipPath(g: number): string {
    const p = groupParts(g);
    const top = g < 2;
    const de = center(p.de);
    const dram = center(p.dram);
    return linePath(
      { x: dram.x, y: top ? p.dram.y + p.dram.h : p.de.y + p.de.h },
      { x: de.x, y: top ? p.de.y : p.dram.y },
    );
  }

  function pdmPath(g: number): string {
    const p = groupParts(g);
    const pdm = center(p.pdm);
    const de = center(p.de);
    return linePath({ x: p.pdm.x + p.pdm.w, y: pdm.y }, { x: p.de.x, y: de.y });
  }

  function l2bPath(l2b: number): string {
    const g = Math.floor(l2b / 2);
    const p = groupParts(g);
    const top = g < 2;
    const b = p.l2bs[l2b % 2];
    const de = center(p.de);
    const l = center(b);
    return linePath(
      { x: de.x, y: top ? p.de.y + p.de.h : p.de.y },
      { x: l.x, y: top ? b.y : b.y + b.h },
    );
  }

  async function openL1b(l1b: number) {
    level = 'l1b';
    const current = app.focusMab;
    const target = l1b * 16 + (Math.floor(current / 16) === l1b ? current % 16 : 0);
    if (target !== current) await app.setFocusMab(target);
  }

  async function openMab(mabInL1b: number) {
    const target = focusL1b * 16 + mabInL1b;
    if (target !== app.focusMab) await app.setFocusMab(target);
  }

  function describe(r: Region | null): string {
    if (!r) return 'PE';
    const full: Record<string, number> = { dram: 4, pdm: 4, l2bm: 8, l1bm: 64 };
    const name = (u: number) =>
      r.mem === 'l2bm' ? `${Math.floor(u / 2)}.${u % 2}` : r.mem === 'l1bm' ? `${u}` : `g${u}`;
    const us =
      r.units.length === full[r.mem] ? '全' : r.units.length > 4 ? `${r.units.length}個` : r.units.map(name).join(',');
    return `${r.mem.toUpperCase()} ${us} [${r.addr}..${r.addr + r.len - 1}]`;
  }

  const COMPUTE_NAME: Record<string, string> = { alu: 'ALU 演算', mau: 'MAU ベクトル演算', matrix: '行列演算' };

  function flowLabel(f: Flow): string {
    if (f.src || f.dst) return `${describe(f.src)} → ${describe(f.dst)}`;
    return f.from === 'matrix' ? 'PE 内の行列レジスタ読み出し' : `PE 内の${COMPUTE_NAME[f.to] ?? f.to}`;
  }

  // ---- detail -----------------------------------------------------------------

  const mabBoxes = $derived.by(() => {
    const out: { mab: number; box: Box }[] = [];
    for (let i = 0; i < 16; i++) {
      const c = i % 4;
      const r = Math.floor(i / 4);
      out.push({ mab: focusL1b * 16 + i, box: { x: 126 + c * 160, y: 62 + r * 88, w: 154, h: 82 } });
    }
    return out;
  });

  function shortWords(words: number[], n = 2): string {
    const s = format(words.slice(0, n), app.view).join(' ');
    return s.length > 14 ? `${s.slice(0, 13)}…` : s;
  }

  function trimText(s: string, n = 8): string {
    return s.length > n ? `${s.slice(0, n - 1)}…` : s;
  }

  interface Summary {
    out: string;
    outAll: string;
    outFirst: string;
    dst: string;
    reads: number;
    writes: number;
    dest?: Access;
  }

  function peSummary(pe: number): Summary {
    const acc = (line?.accesses ?? []).filter((a) => a.unit === pe);
    const outs = acc.filter((a) => a.loc === 'out' && a.write);
    const out = outs[outs.length - 1];
    const writes = acc.filter((a) => a.write && a.loc !== 'out');
    const reads = acc.filter((a) => !a.write);
    const dst = writes[0];
    const values = out ? format(out.words, app.view) : [];
    return {
      out: values.slice(0, 2).join(' '),
      outAll: values.join(' '),
      outFirst: values[0] ?? '',
      dst: dst ? `${dst.loc}[${dst.addr ?? '—'}]` : '',
      reads: reads.length,
      writes: writes.length,
      dest: dst,
    };
  }

  function selectPe(index: number) {
    app.setPeIndex(index);
    const s = peSummary(peBase + index);
    if (s.dest) app.selection = { unit: peBase + index, loc: s.dest.loc, addr: s.dest.addr, line: app.line };
  }

  const l1bmAddrs = $derived.by(() => {
    const addrs = new Set<number>();
    for (const a of line?.accesses ?? []) {
      if ((a.loc === 'l1bm' || a.loc === 'l1bm_src') && a.addr !== null) addrs.add(a.addr);
    }
    if (!addrs.size) for (let i = 0; i < 8; i++) addrs.add(i);
    return [...addrs].sort((a, b) => a - b).slice(0, 8);
  });

  const l1bmRows = $derived.by(() =>
    l1bmAddrs.map((addr) => {
      const hi = read(app.after, `l1b:${focusL1b}`, 'l1bm', addr * 2) ?? 0;
      const lo = read(app.after, `l1b:${focusL1b}`, 'l1bm', addr * 2 + 1) ?? 0;
      const touched = (line?.accesses ?? []).some(
        (a) => (a.loc === 'l1bm' || a.loc === 'l1bm_src') && a.addr === addr,
      );
      return { addr, words: [hi, lo], touched };
    }),
  );

  const matrixRows = $derived.by(() =>
    (line?.accesses ?? [])
      .filter((a) => (a.loc === 'matx' || a.loc === 'maty') && a.unit === focusMab)
      .slice(0, 4),
  );

  const detailFlows = $derived.by(() =>
    flows.filter((f) => {
      if (!f.src && !f.dst) return true;
      for (const r of [f.src, f.dst]) {
        if (!r) continue;
        if (r.mem === 'l1bm' && r.units.includes(focusL1b)) return true;
        if (r.mem === 'l2bm' && r.units.includes(focusL2b)) return true;
        if ((r.mem === 'dram' || r.mem === 'pdm') && r.units.includes(focusGroup)) return true;
      }
      return false;
    }),
  );

  const l1bmAccess = $derived.by(() => {
    const acc = line?.accesses ?? [];
    return {
      read: acc.some((a) => a.loc === 'l1bm_src'),
      write: acc.some((a) => a.loc === 'l1bm' && a.write),
    };
  });

  function rowKey(ev: KeyboardEvent, fn: () => void) {
    if (ev.key === 'Enter' || ev.key === ' ') {
      ev.preventDefault();
      fn();
    }
  }
</script>

<section class="chip">
  <header>
    <button class:on={level === 'chip'} onclick={() => (level = 'chip')}>チップ全体</button>
    {#if level === 'l1b'}
      <span class="crumb">Group {focusGroup} / L2B {focusL2b} / L1B {focusL1b}</span>
      <div class="tabs">
        {#each Array(8) as _, i}
          {@const l1b = focusL2b * 8 + i}
          <button class:on={l1b === focusL1b} onclick={() => openL1b(l1b)}>{i}</button>
        {/each}
      </div>
      <span class="crumb muted">MAB {focusMab} を記録中</span>
    {:else}
      <span class="crumb">Group {focusGroup} / L2B {focusL2b} / L1B {focusL1b} / MAB {focusMab} を選択中</span>
      <button onclick={() => openL1b(focusL1b)}>この L1B を開く</button>
      {#if focusValue}<span class="peek">PE {peBase + app.peIndex}: {focusValue}</span>{/if}
    {/if}
    <span class="legend">
      {#each Object.entries(CATEGORY_NAMES) as [c, name]}
        <i style:background={CATEGORY_COLORS[c]}></i>{name}
      {/each}
    </span>
  </header>

  {#if level === 'chip'}
    <svg viewBox="0 0 {W} {H}" preserveAspectRatio="xMidYMin meet">
      <!-- Groups and their trunk paths. -->
      {#each [0, 1, 2, 3] as g}
        {@const p = groupParts(g)}
        {@const gc = colorOf(active.groups.get(g))}
        <g class="group" class:hot={Boolean(gc)}>
          <rect class="gbox" x={p.x} y={p.y} width={GW} height={GH} rx="6" style:stroke={gc ?? undefined} />
          <text class="glabel" x={p.x + 8} y={g < 2 ? p.y + 13 : p.y + GH - 5}>Group {g}</text>

          <path class="trunk" d={offchipPath(g)} />
          <path class="trunk" d={pdmPath(g)} />
          {#if gc}
            <path class="live" d={offchipPath(g)} style:stroke={gc} />
            <path class="live" d={pdmPath(g)} style:stroke={gc} />
            {#if pulse >= 0}
              <path class="pulsepath" d={offchipPath(g)} pathLength="1" style:stroke={gc} style:stroke-dashoffset={0.08 - pulse * 1.08} />
              <path class="pulsepath" d={pdmPath(g)} pathLength="1" style:stroke={gc} style:stroke-dashoffset={0.08 - pulse * 1.08} />
            {/if}
          {/if}

          <rect class="dram" x={p.dram.x} y={p.dram.y} width={p.dram.w} height={p.dram.h} rx="2" />
          <text class="clabel" x={p.dram.x + p.dram.w / 2} y={p.dram.y + 11}>DRAM I/F</text>
          <rect class="pdm" x={p.pdm.x} y={p.pdm.y} width={p.pdm.w} height={p.pdm.h} rx="2" />
          <text class="clabel" x={p.pdm.x + p.pdm.w / 2} y={p.pdm.y + 18}>PDM</text>
          <rect class="de" x={p.de.x} y={p.de.y} width={p.de.w} height={p.de.h} rx="2" />
          <text class="clabel" x={p.de.x + p.de.w / 2} y={p.de.y + 12}>Data Engine</text>

          {#each [0, 1] as i}
            {@const b = p.l2bs[i]}
            {@const l2b = g * 2 + i}
            {@const lc = colorOf(active.l2bs.get(l2b))}
            <path class="trunk" d={l2bPath(l2b)} />
            {#if lc}
              <path class="live" d={l2bPath(l2b)} style:stroke={lc} />
              {#if pulse >= 0}
                <path class="pulsepath" d={l2bPath(l2b)} pathLength="1" style:stroke={lc} style:stroke-dashoffset={0.08 - pulse * 1.08} />
              {/if}
            {/if}
            <rect class="l2b" x={b.x} y={b.y} width={b.w} height={b.h} rx="4" style:stroke={lc ?? undefined} />
            <text class="clabel" x={b.x + 8} y={b.y + 10}>L2B {l2b}</text>
            <rect class="l2bm" x={b.x + 4} y={b.y + 14} width={b.w - 8} height="7" rx="1" />
            <rect class="ru" x={b.x + 4} y={b.y + 23} width={b.w - 8} height="6" rx="1" />
            <text class="barlabel" x={b.x + 12} y={b.y + 20}>L2BM</text>
          {/each}
        </g>
      {/each}

      <!-- L1B tiles with their 16 MAB dots. -->
      {#each tiles as t (t.l1b)}
        {@const c = colorOf(active.l1bs.get(t.l1b))}
        {@const focus = t.l1b === focusL1b}
        <g
          class="tile"
          class:focus
          role="button"
          tabindex="0"
          onclick={() => openL1b(t.l1b)}
          onkeydown={(e) => rowKey(e, () => openL1b(t.l1b))}
        >
          <title>Group {t.group} / L2B {t.l2b} / L1B {t.l1b}: クリックで 16 MAB を表示</title>
          <rect class="l1b" x={t.box.x} y={t.box.y} width={t.box.w} height={t.box.h} rx="2" style:stroke={c ?? undefined} />
          {#if c}
            <rect class="activefill" x={t.box.x} y={t.box.y} width={t.box.w} height={t.box.h} rx="2" style:fill={c} />
          {/if}
          <rect class="l1bm" x={t.box.x + t.box.w - 4} y={t.box.y + 3} width="3" height={t.box.h - 6} rx="1" />
          {#each Array(16) as _, m}
            <rect
              class="mabdot"
              class:focusmab={t.l1b * 16 + m === focusMab}
              x={t.box.x + 5 + (m % 4) * 6}
              y={t.box.y + 5 + Math.floor(m / 4) * 6}
              width="5"
              height="5"
            />
          {/each}
          <text class="l1label" x={t.box.x + 30} y={t.box.y + 19}>L1B {t.l1b}</text>
          <text class="l1sub" x={t.box.x + 30} y={t.box.y + 32}>16 MAB</text>
          {#if c && pulse >= 0 && t.l1b === focusL1b}
            <circle class="pulse" cx={t.box.x + 36} cy={t.box.y + 26} r={2 + pulse * 7} style:stroke={c} />
          {/if}
        </g>
      {/each}

      {#if active.compute && pulse >= 0}
        {@const t = tiles[focusL1b]}
        <circle class="pulse compute" cx={t.box.x + 10} cy={t.box.y + 10} r={2 + pulse * 6} />
      {/if}

      <text class="note" x={W - 8} y={H - 6} text-anchor="end">
        四角 = L1B（中の小さい 16 個 = MAB）。クリックで L1B を開く。青 = Layer Block、黄 = Memory、灰 = Processing。色付き線 = この行の転送。
      </text>
    </svg>
  {:else}
    {@const l1c = colorOf(active.l1bs.get(focusL1b))}
    {@const focusBox = mabBoxes[focusMab % 16].box}
    <svg viewBox="0 0 {W} {H}" preserveAspectRatio="xMidYMin meet">

      <!-- L1B context: reduction unit, L2BM, and the shared L1BM strip. -->
      <rect class="l2ctx" x={8} y={8} width={766} height={404} rx="5" />
      <text class="glabel" x={16} y={22}>L1B {focusL1b}（Group {focusGroup} / L2B {focusL2b}）</text>
      <rect class="ru" x={126} y={30} width={640} height="12" rx="1" />
      <text class="clabel" x={446} y={39}>Reduction Unit</text>
      <rect class="l2bm" x={126} y={46} width={640} height="10" rx="1" />
      <text class="clabel" x={446} y={54}>L2BM（L2B 共有）</text>

      <!-- L1BM strip. -->
      <rect class="l1bmstrip" x={16} y={66} width="98" height="338" rx="3" />
      <text class="glabel" x={22} y={80}>L1BM</text>
      {#each l1bmRows as row, i}
        <g class="l1brow" class:touched={row.touched}>
          <rect x={20} y={88 + i * 38} width="90" height="34" rx="2" />
          <text class="addr" x={24} y={101 + i * 38}>[{row.addr}]</text>
          {#if row.touched}
            <rect class="touchbar" x={54} y={107 + i * 38} width="52" height="5" rx="2" />
          {/if}
        </g>
      {/each}

      <!-- 16 MAB tiles. -->
      {#each mabBoxes as m}
        {@const focus = m.mab === focusMab}
        <g
          class="mab"
          class:focus
          role="button"
          tabindex="0"
          onclick={() => openMab(m.mab % 16)}
          onkeydown={(e) => rowKey(e, () => openMab(m.mab % 16))}
        >
          <title>MAB {m.mab} を記録する</title>
          <rect x={m.box.x} y={m.box.y} width={m.box.w} height={m.box.h} rx="3" />
          <text class="mablabel" x={m.box.x + 5} y={m.box.y + 12}>MAB {m.mab}</text>
          {#each [0, 1, 2, 3] as i}
            {@const pe = m.mab * 4 + i}
            {@const pc = i % 2}
            {@const pr = Math.floor(i / 2)}
            {@const s = focus ? peSummary(pe) : null}
            <g class="pecell" class:selpe={focus && i === app.peIndex}>
              <rect x={m.box.x + 8 + pc * 68} y={m.box.y + 18 + pr * 26} width="62" height="21" rx="2" />
              <text class="petag" x={m.box.x + 12 + pc * 68} y={m.box.y + 32 + pr * 26}>P{i}</text>
              {#if s}
                <text class="peval" x={m.box.x + 28 + pc * 68} y={m.box.y + 32 + pr * 26}>{trimText(s.outFirst, 7) || s.dst || '—'}</text>
              {/if}
            </g>
          {/each}
          <rect class="mau" x={m.box.x + 5} y={m.box.y + 76} width={m.box.w - 10} height="5" rx="1" />
        </g>
      {/each}

      <!-- Movement in this L1B and from L2BM. -->
      <path class="trunk" d={linePath({ x: 126, y: 56 }, { x: 65, y: 66 })} />
      <path class="trunk" d={linePath({ x: 114, y: 120 }, { x: focusBox.x, y: focusBox.y + focusBox.h / 2 })} />
      {#if l1c}
        <path class="live" d={linePath({ x: 126, y: 56 }, { x: 65, y: 66 })} style:stroke={l1c} />
        {#if pulse >= 0}
          <path class="pulsepath" d={linePath({ x: 126, y: 56 }, { x: 65, y: 66 })} pathLength="1" style:stroke={l1c} style:stroke-dashoffset={0.08 - pulse * 1.08} />
        {/if}
      {/if}
      {#if l1bmAccess.read || l1bmAccess.write}
        <path class="live" d={linePath({ x: 114, y: 120 }, { x: focusBox.x, y: focusBox.y + focusBox.h / 2 })} style:stroke={CATEGORY_COLORS.l1} />
        {#if pulse >= 0}
          <path class="pulsepath" d={linePath({ x: 114, y: 120 }, { x: focusBox.x, y: focusBox.y + focusBox.h / 2 })} pathLength="1" style:stroke={CATEGORY_COLORS.l1} style:stroke-dashoffset={0.08 - pulse * 1.08} />
        {/if}
      {/if}


      <!-- Right panel: focus MAB's PE values, L1BM and matrix registers. -->
      <rect class="focuspanel" x={784} y={8} width={408} height={404} rx="5" />
      <text class="glabel" x={792} y={24}>MAB {focusMab} の 4 PE（{line?.lineno}行目）</text>
      {#each [0, 1, 2, 3] as i}
        {@const pe = peBase + i}
        {@const s = peSummary(pe)}
        {@const pc = i % 2}
        {@const pr = Math.floor(i / 2)}
        <g
          class="pecard"
          class:sel={i === app.peIndex}
          role="button"
          tabindex="0"
          onclick={() => selectPe(i)}
          onkeydown={(e) => rowKey(e, () => selectPe(i))}
        >
          <rect x={792 + pc * 200} y={32 + pr * 86} width="192" height="80" rx="4" />
          <title>{s.outAll}</title>
          <text class="petag" x={800 + pc * 200} y={44 + pr * 86}>PE {pe}（MAB 内 {i}）</text>
          <text class="peval" x={800 + pc * 200} y={58 + pr * 86}>結果 {s.out || '—'}</text>
          <text class="peval" x={800 + pc * 200} y={72 + pr * 86}>書込 {s.dst || '—'}</text>
          <text class="peval small" x={800 + pc * 200} y={86 + pr * 86}>読出 {s.reads}・書込 {s.writes}</text>
        </g>
      {/each}

      <text class="glabel" x={792} y={218}>L1BM の値（この L1B 共有・現在行の番地）</text>
      {#each l1bmRows as row, i}
        <g class="l1brow" class:touched={row.touched}>
          <rect x={792} y={226 + i * 18} width="392" height="16" rx="2" />
          <text class="addr" x={798} y={238 + i * 18}>[{row.addr}]</text>
          <text class="val" x={846} y={238 + i * 18}>{format(row.words, app.view).join(' ')}</text>
        </g>
      {/each}

      <text class="glabel" x={792} y={382}>行列レジスタ（現在行）</text>
      {#each matrixRows as m, i}
        <text class="val" x={798 + i * 100} y={396}>{m.loc}[{m.addr}] = {shortWords(m.words, 4)}</text>
      {:else}
        <text class="muted" x={798} y={396}>この行では行列レジスタを書きません</text>
      {/each}
    </svg>
  {/if}

  <div class="flows">
    {#each (level === 'l1b' ? detailFlows : flows) as f}
      <span class="flow" style:border-color={CATEGORY_COLORS[category(f.from, f.to)]}>
        {flowLabel(f)}
        <em>{f.kind}</em>
        <b>{volume(f.longs)}</b>
      </span>
    {:else}
      <span class="muted">この行には転送も演算もありません</span>
    {/each}
  </div>
</section>

<style>
  .chip {
    display: flex;
    flex-direction: column;
    min-height: 0;
    min-width: 0;
    gap: 2px;
  }
  header {
    display: flex;
    align-items: center;
    gap: 8px;
    padding: 2px 8px;
    font-size: 11px;
    flex-wrap: wrap;
  }
  header button {
    padding: 1px 6px;
    font-size: 11px;
  }
  header button.on {
    background: var(--accent);
    color: var(--bg);
  }
  .crumb {
    font-family: var(--mono);
    color: var(--fg);
  }
  .tabs {
    display: flex;
    gap: 2px;
    margin-left: 4px;
  }
  .tabs button {
    min-width: 1.6em;
    padding: 1px 3px;
  }
  .legend {
    margin-left: auto;
    display: flex;
    gap: 4px;
    align-items: center;
    color: var(--muted);
  }
  .legend i {
    display: inline-block;
    width: 8px;
    height: 8px;
    border-radius: 2px;
    margin-left: 6px;
  }
  svg {
    width: 100%;
    flex: 1 1 0;
    min-height: 0;
    height: 0;
    display: block;
  }
  text {
    font-size: 10px;
    fill: var(--fg);
  }
  .gbox {
    fill: color-mix(in srgb, var(--panel) 70%, transparent);
    stroke: var(--line);
    stroke-width: 1;
  }
  .group.hot .gbox {
    fill: color-mix(in srgb, var(--accent) 4%, var(--panel));
  }
  .glabel {
    font-size: 11px;
    font-weight: 600;
    fill: var(--muted);
  }
  .clabel {
    font-size: 10px;
    text-anchor: middle;
    fill: var(--fg);
  }
  .barlabel {
    font-size: 8px;
    fill: var(--muted);
  }
  .peek {
    color: var(--accent);
    font-family: var(--mono);
  }
  .dram,
  .de {
    fill: #c9cdd2;
    stroke: #9aa1ab;
  }
  .pdm,
  .l2bm,
  .l1bm {
    fill: #fde9b8;
    stroke: #d9b86c;
  }
  .l2b {
    fill: #dce8fb;
    stroke: #9db8df;
  }
  .ru,
  .mau {
    fill: #c9cdd2;
    stroke: #9aa1ab;
  }
  .l1b {
    fill: #eef4fe;
    stroke: #9db8df;
  }
  .activefill {
    fill-opacity: 0.22;
    stroke: none;
  }
  .mabdot {
    fill: #6f8fbd;
  }
  .mabdot.focusmab {
    fill: var(--accent);
    stroke: var(--bg);
    stroke-width: 0.8;
  }
  .l1label {
    font-size: 9px;
    font-weight: 600;
  }
  .l1sub {
    font-size: 8px;
    fill: var(--muted);
  }
  .tile {
    cursor: pointer;
  }
  .tile.focus .l1b {
    stroke: var(--accent);
    stroke-width: 2;
  }
  .tile:hover .l1b {
    stroke: var(--accent);
  }
  .trunk {
    fill: none;
    stroke: var(--line);
    stroke-width: 1;
  }
  .live {
    fill: none;
    stroke-width: 2;
    opacity: 0.7;
  }
  .pulse {
    fill: none;
    stroke-width: 2;
    opacity: 0.9;
  }
  .pulsepath {
    fill: none;
    stroke-width: 3;
    stroke-dasharray: 0.08 1;
    stroke-linecap: round;
  }
  .pulse.compute {
    stroke: var(--c-compute);
  }
  .note {
    font-size: 9px;
    fill: var(--muted);
  }
  .flows {
    display: flex;
    flex: none;
    flex-wrap: wrap;
    gap: 3px 10px;
    max-height: 36px;
    overflow: auto;
    padding: 0 8px 4px;
    font-size: 10px;
  }
  .flow {
    border-left: 3px solid;
    padding-left: 5px;
    white-space: nowrap;
  }
  .flow em {
    color: var(--muted);
    font-style: normal;
    margin-left: 4px;
  }
  .flow b {
    color: var(--muted);
    font-weight: 400;
    margin-left: 4px;
  }
  .muted {
    color: var(--muted);
  }

  /* detail */
  .l2ctx,
  .focuspanel {
    fill: color-mix(in srgb, var(--panel) 60%, transparent);
    stroke: var(--line);
  }
  .l1bmstrip {
    fill: #fdf3d9;
    stroke: #d9b86c;
  }
  .l1brow rect {
    fill: transparent;
  }
  .l1brow.touched rect:first-child {
    fill: color-mix(in srgb, var(--c-l1) 18%, transparent);
  }
  .touchbar {
    fill: var(--c-l1);
  }
  .addr {
    font-family: var(--mono);
    font-size: 9px;
    fill: var(--muted);
  }
  .val {
    font-family: var(--mono);
    font-size: 10px;
  }
  .mab {
    cursor: pointer;
  }
  .mab > rect:first-of-type {
    fill: #eef4fe;
    stroke: #9db8df;
  }
  .mab.focus > rect:first-of-type {
    fill: #dfeafd;
    stroke: var(--accent);
    stroke-width: 2;
  }
  .mablabel {
    font-size: 11px;
    font-weight: 600;
    fill: var(--muted);
  }
  .pecell > rect {
    fill: var(--panel);
    stroke: var(--line);
  }
  .pecell.selpe > rect {
    stroke: var(--accent);
    stroke-width: 1.5;
  }
  .petag {
    font-family: var(--mono);
    font-size: 9px;
    fill: var(--muted);
  }
  .peval {
    font-family: var(--mono);
    font-size: 10px;
  }
  .peval.small {
    font-size: 9px;
    fill: var(--muted);
  }
  .pecard {
    cursor: pointer;
  }
  .pecard > rect {
    fill: var(--panel);
    stroke: var(--line);
  }
  .pecard.sel > rect {
    stroke: var(--accent);
    stroke-width: 2;
  }
</style>
