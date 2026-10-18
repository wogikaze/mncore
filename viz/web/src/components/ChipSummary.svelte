<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { CATEGORY_COLORS, CATEGORY_NAMES, category } from '../lib/flows';
  import { activityOf, levelName } from '../lib/hierarchy';
  import { volume } from '../lib/numbers';
  import type { Flow } from '../lib/types';

  const trace = $derived(app.trace);
  const line = $derived(trace?.lines[app.line]);
  const flows = $derived(line?.flows ?? []);
  const act = $derived(activityOf(flows));

  interface GroupInfo {
    id: number;
    l1bs: number[];
    l2bs: number[];
    cats: Set<string>;
    volume: number;
  }

  const groups = $derived.by<GroupInfo[]>(() => {
    const out: GroupInfo[] = [0, 1, 2, 3].map((id) => ({ id, l1bs: [], l2bs: [], cats: new Set(), volume: 0 }));
    for (const f of flows) {
      const c = category(f.from, f.to);
      for (const r of [f.src, f.dst]) {
        if (!r) continue;
        if (r.mem === 'l1bm') {
          for (const u of r.units) out[Math.floor(u / 16)].l1bs.push(u);
        } else if (r.mem === 'l2bm') {
          for (const u of r.units) out[Math.floor(u / 2)].l2bs.push(u);
        } else if (r.mem === 'dram' || r.mem === 'pdm') {
          for (const u of r.units) out[u].cats.add(c);
        }
      }
      if (f.src || f.dst) {
        for (const g of out) {
          const touches = [f.src, f.dst].some((r) => {
            if (!r) return false;
            if (r.mem === 'l1bm') return r.units.some((u) => Math.floor(u / 16) === g.id);
            if (r.mem === 'l2bm') return r.units.some((u) => Math.floor(u / 2) === g.id);
            if (r.mem === 'dram' || r.mem === 'pdm') return r.units.includes(g.id);
            return false;
          });
          if (touches) {
            g.volume += f.longs;
            g.cats.add(c);
          }
        }
      }
    }
    for (const g of out) {
      g.l1bs = [...new Set(g.l1bs)].sort((a, b) => a - b);
      g.l2bs = [...new Set(g.l2bs)].sort((a, b) => a - b);
    }
    return out;
  });

  function ranges(units: number[]): string {
    if (!units.length) return '—';
    const out: string[] = [];
    let start = units[0];
    let prev = units[0];
    for (const u of units.slice(1)) {
      if (u === prev + 1) {
        prev = u;
      } else {
        out.push(start === prev ? `${start}` : `${start}–${prev}`);
        start = prev = u;
      }
    }
    out.push(start === prev ? `${start}` : `${start}–${prev}`);
    return out.join(', ');
  }

  function open(g: number) {
    app.selectGroup(g);
  }
</script>

<section class="chipview">
  <header>
    <div>
      <h3>チップ全体の転送</h3>
      <span class="sub">{line?.lineno}行目・step {line?.step}・Group / L1B の活動と転送量</span>
    </div>
    <div class="legend">
      {#each Object.entries(CATEGORY_COLORS) as [c, col]}
        <span><i style:background={col}></i>{CATEGORY_NAMES[c]}</span>
      {/each}
    </div>
  </header>

  <div class="groups">
    {#each groups as g (g.id)}
      <button class="gcard" class:active={g.l1bs.length > 0 || g.l2bs.length > 0 || g.cats.size > 0} onclick={() => open(g.id)}>
        <div class="ghead">
          <b>Group {g.id}</b>
          <span>{g.l1bs.length}/16 L1B</span>
        </div>
        <div class="bars">
          {#each [...g.cats] as c}
            <span class="bar" style:background={CATEGORY_COLORS[c]} title={CATEGORY_NAMES[c]}></span>
          {/each}
        </div>
        <div class="line">
          <span class="k">L2B</span> <span>{ranges(g.l2bs)}</span>
        </div>
        <div class="line">
          <span class="k">L1B</span> <span>{ranges(g.l1bs)}</span>
        </div>
        <div class="vol">{g.volume ? `${volume(g.volume)} 転送` : '転送なし'}</div>
      </button>
    {/each}
  </div>

  <div class="flows">
    <h4>この行の転送</h4>
    {#each flows as f, i (i)}
      <div class="flow" style:border-color={CATEGORY_COLORS[category(f.from, f.to)]}>
        <span class="cat">{CATEGORY_NAMES[category(f.from, f.to)]}</span>
        <span>{levelName(f.from)} → {levelName(f.to)}</span>
        <span class="kind">{f.kind}</span>
        <b>{volume(f.longs)}</b>
      </div>
    {:else}
      <span class="muted">この行には転送がありません（PE 内の演算のみ）。</span>
    {/each}
  </div>
</section>

<style>
  .chipview {
    display: flex;
    flex-direction: column;
    min-height: 0;
    min-width: 0;
    padding: 8px 10px;
    gap: 6px;
    overflow: auto;
  }
  header {
    display: flex;
    align-items: baseline;
    gap: 16px;
    flex: none;
    flex-wrap: wrap;
  }
  h3 {
    margin: 0;
    font-size: 15px;
  }
  .sub {
    color: var(--muted);
    font-size: 11px;
  }
  .legend {
    margin-left: auto;
    display: flex;
    gap: 8px;
    color: var(--muted);
    font-size: 10px;
  }
  .legend i {
    display: inline-block;
    width: 7px;
    height: 7px;
    border-radius: 2px;
    margin-right: 2px;
  }
  .groups {
    display: grid;
    grid-template-columns: 1fr 1fr;
    gap: 6px;
    flex: none;
  }
  .gcard {
    display: flex;
    flex-direction: column;
    gap: 3px;
    text-align: left;
    padding: 6px 8px;
    background: var(--panel-2);
    border: 1px solid var(--line);
    border-radius: 5px;
    min-height: 84px;
  }
  .gcard:hover {
    border-color: var(--accent);
  }
  .gcard.active {
    border-color: color-mix(in srgb, var(--accent) 50%, var(--line));
  }
  .ghead {
    display: flex;
    justify-content: space-between;
    align-items: baseline;
  }
  .ghead b {
    font-size: 13px;
  }
  .ghead span {
    color: var(--muted);
    font-size: 10px;
  }
  .bars {
    display: flex;
    height: 4px;
    gap: 2px;
    margin: 2px 0;
  }
  .bar {
    flex: 1;
    border-radius: 2px;
  }
  .line {
    font-family: var(--mono);
    font-size: 10px;
    color: var(--fg);
    white-space: nowrap;
    overflow: hidden;
    text-overflow: ellipsis;
  }
  .k {
    color: var(--muted);
    display: inline-block;
    width: 30px;
  }
  .vol {
    color: var(--muted);
    font-size: 10px;
    margin-top: auto;
  }
  .flows {
    flex: 1;
    min-height: 0;
    border-top: 1px solid var(--line);
    padding-top: 4px;
    overflow: auto;
  }
  h4 {
    margin: 0 0 3px;
    font-size: 10px;
    color: var(--muted);
    letter-spacing: 0.04em;
  }
  .flow {
    display: flex;
    align-items: baseline;
    gap: 8px;
    border-left: 3px solid;
    padding: 1px 6px;
    font-family: var(--mono);
    font-size: 10px;
    white-space: nowrap;
  }
  .flow .cat {
    color: var(--muted);
    min-width: 64px;
  }
  .flow .kind {
    color: var(--muted);
  }
  .flow b {
    margin-left: auto;
    color: var(--muted);
    font-weight: 400;
  }
  .muted {
    color: var(--muted);
    font-size: 11px;
  }
</style>
