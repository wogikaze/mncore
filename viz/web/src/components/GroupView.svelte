<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { CATEGORY_COLORS, category } from '../lib/flows';
  import { activityOf, l1bOfMab, levelName } from '../lib/hierarchy';
  import { volume } from '../lib/numbers';

  const trace = $derived(app.trace);
  const line = $derived(trace?.lines[app.line]);
  const group = $derived(app.focusGroup);
  const focusMab = $derived(app.focusMab);
  const act = $derived(activityOf(line?.flows ?? []));
  const l1bs = $derived(Array.from({ length: 16 }, (_, i) => group * 16 + i));

  const flows = $derived(
    (line?.flows ?? []).filter((f) => {
      if (!f.src && !f.dst) return true;
      return [f.src, f.dst].some((r) => {
        if (!r) return false;
        if (r.mem === 'l1bm') return r.units.some((u) => Math.floor(u / 16) === group);
        if (r.mem === 'l2bm') return r.units.some((u) => Math.floor(u / 2) === group);
        if (r.mem === 'dram' || r.mem === 'pdm') return r.units.includes(group);
        return false;
      });
    }),
  );

  function colorOf(c: string | undefined) {
    return c ? CATEGORY_COLORS[c] : undefined;
  }

  function open(l1b: number) {
    app.selectL1b(l1b);
  }
</script>

<section class="groupview">
  <header>
    <div>
      <h3>Group {group}</h3>
      <span class="sub">L2B {group * 2}–{group * 2 + 1}・L1B {group * 16}–{group * 16 + 15}・{line?.lineno}行目</span>
    </div>
    <div class="flowline">
      {#each flows as f}
        <span class="flow" style:border-color={CATEGORY_COLORS[category(f.from, f.to)]}>
          {levelName(f.from)} → {levelName(f.to)} <em>{f.kind}</em> <b>{volume(f.longs)}</b>
        </span>
      {:else}
        <span class="muted">この行に関係する転送はありません</span>
      {/each}
    </div>
  </header>

  <div class="l2bs">
    {#each [0, 1] as side}
      {@const l2b = group * 2 + side}
      <section class="l2b">
        <h4>L2B {l2b} <span>L1B {l2b * 8}–{l2b * 8 + 7}</span></h4>
        <div class="tiles">
          {#each Array(8) as _, i}
            {@const l1b = l2b * 8 + i}
            {@const c = colorOf(act.l1bs.get(l1b))}
            {@const current = l1bOfMab(focusMab) === l1b}
            <button class="tile" class:active={Boolean(c)} class:current onclick={() => open(l1b)}>
              <div class="tilehead">
                <b>L1B {l1b}</b>
                {#if current}<span class="badge">現在</span>{/if}
              </div>
              <div class="dots">
                {#each Array(16) as _, m}
                  <i class:focus={l1b * 16 + m === focusMab}></i>
                {/each}
              </div>
              <div class="meta">16 MAB</div>
              {#if c}<span class="bar" style:background={c}></span>{/if}
            </button>
          {/each}
        </div>
      </section>
    {/each}
  </div>
</section>

<style>
  .groupview {
    display: flex;
    flex-direction: column;
    min-height: 0;
    min-width: 0;
    padding: 8px 10px;
    gap: 8px;
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
  .flowline {
    margin-left: auto;
    display: flex;
    gap: 6px;
    flex-wrap: wrap;
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
  }
  .flow b {
    color: var(--muted);
    font-weight: 400;
  }
  .l2bs {
    flex: 1;
    min-height: 0;
    display: grid;
    grid-template-columns: 1fr 1fr;
    gap: 10px;
  }
  .l2b {
    display: flex;
    flex-direction: column;
    min-height: 0;
    gap: 4px;
    background: var(--panel);
    border: 1px solid var(--line);
    border-radius: 5px;
    padding: 6px;
  }
  h4 {
    margin: 0;
    font-size: 11px;
    color: var(--fg);
  }
  h4 span {
    color: var(--muted);
    font-weight: 400;
    margin-left: 4px;
  }
  .tiles {
    flex: 1;
    min-height: 0;
    display: grid;
    grid-template-columns: 1fr 1fr;
    grid-template-rows: repeat(4, 1fr);
    gap: 4px;
  }
  .tile {
    position: relative;
    display: flex;
    flex-direction: column;
    min-height: 0;
    padding: 3px 5px;
    text-align: left;
    background: var(--panel-2);
    border: 1px solid var(--line);
    border-radius: 4px;
    gap: 2px;
    overflow: hidden;
  }
  .tile:hover {
    border-color: var(--accent);
  }
  .tile.active {
    border-color: color-mix(in srgb, var(--accent) 60%, var(--line));
  }
  .tile.current {
    border-color: var(--accent);
    box-shadow: inset 3px 0 var(--accent);
  }
  .tilehead {
    display: flex;
    justify-content: space-between;
    align-items: baseline;
  }
  .tilehead b {
    font-family: var(--mono);
    font-size: 10px;
  }
  .badge {
    font-size: 8px;
    color: var(--accent);
  }
  .dots {
    display: grid;
    grid-template-columns: repeat(8, 1fr);
    gap: 1px;
    max-width: 120px;
  }
  .dots i {
    width: 4px;
    height: 4px;
    background: color-mix(in srgb, var(--fg) 28%, transparent);
    border-radius: 1px;
  }
  .dots i.focus {
    background: var(--accent);
  }
  .meta {
    color: var(--muted);
    font-size: 8px;
  }
  .bar {
    position: absolute;
    left: 0;
    top: 0;
    bottom: 0;
    width: 3px;
  }
  .muted {
    color: var(--muted);
  }
</style>
