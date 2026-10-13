<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { volume } from '../lib/numbers';
  import { CATEGORY_COLORS, CATEGORY_NAMES, category } from '../lib/flows';

  const W = 1000;
  const H = 56;
  const trace = $derived(app.trace);

  // One bar per line that occupies steps: stacked log-volume per category.
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
      const w = Math.max(0.6, (l.words / total) * W - 0.3);
      let y = H;
      const parts = Object.entries(sums).map(([c, v]) => {
        const h = Math.min(H / 2, Math.log2(1 + v) * 1.4);
        y -= h;
        return { c, y, h, v };
      });
      return [{ i, x, w, parts, nop: l.kind === 'nop', mv: l.kind === 'mv' }];
    });
  });

  const cursor = $derived.by(() => {
    if (!trace) return 0;
    const l = trace.lines[app.line];
    return ((l?.step ?? 0) / Math.max(1, trace.score)) * W;
  });

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
  }

  // Playback: advance one line per step duration.
  $effect(() => {
    if (!app.playing) return;
    const words = trace?.lines[app.line]?.words || 1;
    const t = setTimeout(() => app.next(), app.stepSeconds * 1000 * Math.min(words, 4));
    return () => clearTimeout(t);
  });

  function onKey(ev: KeyboardEvent) {
    if ((ev.target as HTMLElement).tagName === 'TEXTAREA') return;
    if (ev.key === 'ArrowRight') app.next();
    else if (ev.key === 'ArrowLeft') app.prev();
    else if (ev.key === ' ') {
      app.playing = !app.playing;
      ev.preventDefault();
    }
  }
</script>

<svelte:window onkeydown={onKey} />

<section class="timeline">
  <div class="controls">
    <button onclick={() => app.prev()} title="前のステップ (←)">◀︎</button>
    <button onclick={() => (app.playing = !app.playing)} title="再生 / 停止 (Space)">{app.playing ? '❚❚' : '▶︎'}</button>
    <button onclick={() => app.next()} title="次のステップ (→)">▶︎|</button>
    <label title="1ステップあたりの秒数">
      速度 <input type="range" min="0.2" max="3" step="0.1" bind:value={app.stepSeconds} /> {app.stepSeconds.toFixed(1)}s
    </label>
    {#if trace}
      {@const l = trace.lines[app.line]}
      <span class="pos">step {l?.step ?? 0} / {trace.score} ・ {l?.lineno}行</span>
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
    aria-valuenow={app.line}
    tabindex="0"
    onpointerdown={(e) => {
      dragging = true;
      (e.currentTarget as Element).setPointerCapture(e.pointerId);
      seekAt(e);
    }}
    onpointermove={(e) => dragging && seekAt(e)}
    onpointerup={() => (dragging = false)}
  >
    {#each bars as b (b.i)}
      {#if b.nop}
        <rect x={b.x} y="0" width={b.w} height={H} class="nopband"><title>nop</title></rect>
      {/if}
      {#each b.parts as p}
        <rect x={b.x} y={p.y} width={b.w} height={p.h} fill={CATEGORY_COLORS[p.c]}>
          <title>{volume(p.v)}</title>
        </rect>
      {/each}
    {/each}
    <line x1={cursor} x2={cursor} y1="0" y2={H} class="cursor" />
  </svg>
</section>

<style>
  .timeline {
    border-top: 1px solid var(--line);
    padding: 4px 8px 6px;
  }
  .controls {
    display: flex;
    align-items: center;
    gap: 8px;
    font-size: 12px;
    margin-bottom: 4px;
  }
  .controls button {
    min-width: 2.2em;
  }
  .pos {
    font-family: var(--mono);
    color: var(--muted);
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
    width: 9px;
    height: 9px;
    border-radius: 2px;
    margin-left: 8px;
  }
  svg {
    width: 100%;
    height: 56px;
    background: var(--panel);
    cursor: pointer;
    touch-action: none;
  }
  .nopband {
    fill: var(--warn-bg);
  }
  .cursor {
    stroke: var(--fg);
    stroke-width: 2;
    vector-effect: non-scaling-stroke;
  }
</style>
