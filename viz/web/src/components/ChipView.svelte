<script lang="ts">
  import gsap from 'gsap';
  import { app } from '../lib/state.svelte';
  import { CATEGORY_COLORS, category } from '../lib/flows';
  import { volume } from '../lib/numbers';
  import type { Flow } from '../lib/types';

  const W = 1000;
  const H = 300;
  type Box = { x: number; y: number; w: number; h: number };
  const center = (b: Box) => ({ x: b.x + b.w / 2, y: b.y + b.h / 2 });

  // Layout of the hierarchy (SDM 1.1): 4 groups, each with DRAM, PDM and 2 L2Bs; 8 L1Bs per
  // L2B; 16 MABs x 4 PEs per L1B.
  const LEFT = 40;
  const groupW = (W - LEFT) / 4;
  const dram: Box[] = [0, 1, 2, 3].map((g) => ({ x: LEFT + g * groupW + 14, y: 22, w: 96, h: 26 }));
  const pdm: Box[] = [0, 1, 2, 3].map((g) => ({ x: LEFT + g * groupW + 126, y: 22, w: 96, h: 26 }));
  const l2bm: Box[] = [...Array(8).keys()].map((k) => ({ x: LEFT + Math.floor(k / 2) * groupW + 14 + (k % 2) * 112, y: 96, w: 96, h: 26 }));
  const l1bm: Box[] = [...Array(64).keys()].map((i) => {
    const p = l2bm[Math.floor(i / 8)];
    return { x: p.x + (i % 8) * 12, y: 168, w: 10, h: 18 };
  });
  const pe: Box[] = l1bm.map((b) => ({ x: b.x, y: 226, w: 10, h: 48 }));

  const focusL1b = $derived(Math.floor(app.focusPe / 64));
  const focusMab = $derived(Math.floor(app.focusPe / 4) % 16);

  function nodes(level: string): Box[] {
    return ({ dram, pdm, l2bm, l1bm, pe } as Record<string, Box[]>)[level] ?? pe;
  }

  /** Source-destination pairs of a flow between two levels, following the tree. */
  function pairs(f: Flow): [Box, Box][] {
    const from = nodes(f.from);
    const to = nodes(f.to);
    const out: [Box, Box][] = [];
    // Index mapping: a node of the upper level covers a block of the lower level.
    const parent = (lvl: string, i: number, upper: string): number => {
      const size: Record<string, number> = { dram: 4, pdm: 4, l2bm: 8, l1bm: 64, pe: 64 };
      return Math.floor((i * size[upper]) / size[lvl]);
    };
    const size = (l: string) => nodes(l).length;
    if (f.from === f.to) {
      // Multicast between L1BMs: neighbors within each L2B.
      for (let i = 0; i < size(f.from); i++) out.push([from[i], to[i % 8 === 7 ? i - 7 : i + 1]]);
    } else if (size(f.from) <= size(f.to)) {
      to.forEach((t, j) => out.push([from[parent(f.to, j, f.from)], t]));
    } else {
      from.forEach((s, j) => out.push([s, to[parent(f.from, j, f.to)]]));
    }
    return out;
  }

  let layer: SVGGElement | undefined = $state();
  let tl: gsap.core.Timeline | null = null;

  const flows = $derived(app.trace?.lines[app.line]?.flows ?? []);
  const words = $derived(app.trace?.lines[app.line]?.words ?? 1);

  $effect(() => {
    const fs = flows;
    const duration = Math.max(0.4, app.stepSeconds * Math.min(words, 4) * 0.85);
    const g = layer;
    if (!g) return;
    tl?.kill();
    g.replaceChildren();
    tl = gsap.timeline();
    const ns = 'http://www.w3.org/2000/svg';
    for (const f of fs) {
      const color = CATEGORY_COLORS[category(f.from, f.to)];
      if (f.to === 'alu' || f.to === 'mau' || f.to === 'matrix' || f.from === 'matrix') {
        // Computation inside PEs: pulse the PE band.
        const r = document.createElementNS(ns, 'rect');
        r.setAttribute('x', String(pe[0].x - 4));
        r.setAttribute('y', String(pe[0].y - 4));
        r.setAttribute('width', String(pe[63].x + pe[63].w - pe[0].x + 8));
        r.setAttribute('height', String(pe[0].h + 8));
        r.setAttribute('rx', '6');
        r.setAttribute('fill', 'none');
        r.setAttribute('stroke', color);
        r.setAttribute('stroke-width', '3');
        g.appendChild(r);
        tl.fromTo(r, { opacity: 0.9 }, { opacity: 0, duration, ease: 'power1.out' }, 0);
        continue;
      }
      const ps = pairs(f);
      // Particles per path grow with the logarithm of the volume.
      const perPath = Math.max(1, Math.min(6, Math.round(Math.log2(1 + f.longs / ps.length) / 2)));
      ps.forEach(([s, d], k) => {
        if (!s || !d) {
          console.warn('no node for flow', f.from, f.to, k);
          return;
        }
        const a = center(s);
        const b = center(d);
        for (let n = 0; n < perPath; n++) {
          const c = document.createElementNS(ns, 'circle');
          c.setAttribute('r', f.kind === 'reduce' ? '2.6' : '2');
          c.setAttribute('fill', color);
          c.setAttribute('cx', String(a.x));
          c.setAttribute('cy', String(a.y));
          c.setAttribute('opacity', '0');
          g.appendChild(c);
          const delay = (n / perPath) * duration * 0.6 + (k % 8) * 0.01;
          tl!.set(c, { opacity: 1 }, delay);
          tl!.to(c, { attr: { cx: b.x, cy: b.y }, duration: duration * 0.4, ease: 'power1.inOut' }, delay);
          tl!.to(c, { opacity: 0, duration: 0.15 }, delay + duration * 0.4);
        }
      });
    }
  });

  const lineFlows = $derived(flows.filter((f) => f.longs > 0));
</script>

<section class="chip">
  <svg viewBox="0 0 {W} {H}">
    {#each [0, 1, 2, 3] as g}
      <rect class="group" x={LEFT + g * groupW + 4} y="6" width={groupW - 12} height="128" rx="8" />
      <text class="glabel" x={LEFT + g * groupW + 10} y="16">group {g}</text>
    {/each}
    {#each dram as b, g}
      <rect class="node dram" x={b.x} y={b.y} width={b.w} height={b.h} rx="4" />
      <text x={b.x + b.w / 2} y={b.y + 17}>DRAM{g}</text>
    {/each}
    {#each pdm as b, g}
      <rect class="node pdm" x={b.x} y={b.y} width={b.w} height={b.h} rx="4" />
      <text x={b.x + b.w / 2} y={b.y + 17}>PDM{g}</text>
    {/each}
    {#each l2bm as b, k}
      <rect class="node l2" x={b.x} y={b.y} width={b.w} height={b.h} rx="4" />
      <text x={b.x + b.w / 2} y={b.y + 17}>L2BM {Math.floor(k / 2)}.{k % 2}</text>
    {/each}
    {#each l1bm as b, i}
      <rect class="node l1" class:focus={i === focusL1b} x={b.x} y={b.y} width={b.w} height={b.h} rx="2">
        <title>L1BM n{Math.floor(i / 16)}c{Math.floor(i / 8) % 2}b{i % 8}</title>
      </rect>
    {/each}
    {#each pe as b, i}
      <rect class="node pe" class:focus={i === focusL1b} x={b.x} y={b.y} width={b.w} height={b.h} rx="2">
        <title>64 PE (16 MAB) of L1B {i}</title>
      </rect>
    {/each}
    <!-- Focus MAB marker within its L1B column. -->
    <rect class="mabmark" x={pe[focusL1b].x - 1} y={pe[focusL1b].y + (focusMab * pe[0].h) / 16} width={pe[0].w + 2} height={pe[0].h / 16 + 1} />
    <text class="lvl" x="4" y={l1bm[0].y + 13}>L1BM</text>
    <text class="lvl" x="4" y={pe[0].y + 26}>PE</text>
    <g bind:this={layer}></g>
  </svg>
  <div class="flows">
    {#each lineFlows as f}
      <span style:border-color={CATEGORY_COLORS[category(f.from, f.to)]}>{f.from} → {f.to} <em>{f.kind}</em> {volume(f.longs)}</span>
    {:else}
      <span class="none">このステップにチップ規模の転送はありません</span>
    {/each}
  </div>
</section>

<style>
  .chip {
    display: flex;
    flex-direction: column;
    min-height: 0;
  }
  svg {
    width: 100%;
    flex: 1;
    min-height: 0;
  }
  .group {
    fill: none;
    stroke: var(--line);
    stroke-dasharray: 3 3;
  }
  .glabel,
  .lvl {
    font-size: 9px;
    fill: var(--muted);
  }
  text {
    font-size: 10px;
    text-anchor: middle;
    fill: var(--fg);
    pointer-events: none;
  }
  .lvl,
  .glabel {
    text-anchor: start;
  }
  .node {
    stroke: var(--line);
    fill: var(--panel);
  }
  .dram,
  .pdm {
    fill: color-mix(in srgb, var(--c-offchip) 14%, var(--panel));
  }
  .l2 {
    fill: color-mix(in srgb, var(--c-l2) 14%, var(--panel));
  }
  .l1 {
    fill: color-mix(in srgb, var(--c-l1) 14%, var(--panel));
  }
  .pe {
    fill: color-mix(in srgb, var(--c-compute) 10%, var(--panel));
  }
  .focus {
    stroke: var(--fg);
    stroke-width: 1.5;
  }
  .mabmark {
    fill: var(--fg);
  }
  .flows {
    display: flex;
    flex-wrap: wrap;
    gap: 6px;
    padding: 4px 8px;
    font-size: 11px;
    min-height: 22px;
  }
  .flows span {
    border-left: 3px solid;
    padding: 0 6px;
    background: var(--panel);
  }
  .flows em {
    color: var(--muted);
    font-style: normal;
  }
  .flows .none {
    border: none;
    color: var(--muted);
    background: none;
  }
</style>
