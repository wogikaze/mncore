<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { format } from '../lib/numbers';
  import { read } from '../lib/memory';
  import { levelName, peSummary } from '../lib/hierarchy';
  import { CATEGORY_COLORS, category } from '../lib/flows';
  import { volume } from '../lib/numbers';

  const trace = $derived(app.trace);
  const line = $derived(trace?.lines[app.line]);
  const l1b = $derived(app.focusL1b);
  const mabBase = $derived(l1b * 16);

  const mabs = $derived(
    Array.from({ length: 16 }, (_, i) => {
      const mab = mabBase + i;
      return {
        i,
        mab,
        focus: mab === app.focusMab,
        pes: [0, 1, 2, 3].map((p) => {
          const pe = mab * 4 + p;
          return { p, pe, s: mab === app.focusMab ? peSummary(line, pe, app.view) : null };
        }),
      };
    }),
  );

  const l1bm = $derived.by(() => {
    const addrs = new Set<number>();
    for (const a of line?.accesses ?? []) {
      if ((a.loc === 'l1bm' || a.loc === 'l1bm_src') && a.addr !== null) addrs.add(a.addr);
    }
    if (!addrs.size) for (let i = 0; i < 8; i++) addrs.add(i);
    return [...addrs]
      .sort((a, b) => a - b)
      .slice(0, 10)
      .map((addr) => {
        const hi = read(app.after, `l1b:${l1b}`, 'l1bm', addr * 2) ?? 0;
        const lo = read(app.after, `l1b:${l1b}`, 'l1bm', addr * 2 + 1) ?? 0;
        const touched = (line?.accesses ?? []).some(
          (a) => (a.loc === 'l1bm' || a.loc === 'l1bm_src') && a.addr === addr,
        );
        return { addr, words: [hi, lo], touched };
      });
  });

  const flows = $derived(
    (line?.flows ?? []).filter((f) => {
      if (!f.src && !f.dst) return true;
      return [f.src, f.dst].some((r) => {
        if (!r) return false;
        if (r.mem === 'l1bm') return r.units.includes(l1b);
        if (r.mem === 'l2bm') return r.units.includes(app.focusL2b);
        if (r.mem === 'dram' || r.mem === 'pdm') return r.units.includes(app.focusGroup);
        return false;
      });
    }),
  );

  function open(i: number) {
    app.selectMab(mabBase + i);
  }
</script>

<section class="l1bview">
  <header>
    <div>
      <h3>L1B {l1b}</h3>
      <span class="sub">Group {app.focusGroup} / L2B {app.focusL2b}・{line?.lineno}行目・MAB {app.focusMab} を記録中</span>
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

  <div class="main">
    <div class="grid">
      {#each mabs as m (m.mab)}
        <button class="mab" class:focus={m.focus} class:active={m.focus && (m.pes.some((p) => p.s && (p.s.readCount || p.s.writeCount)))} onclick={() => open(m.i)}>
          <div class="mhead">
            <b>MAB {m.mab}</b>
            {#if m.focus}<span class="badge">記録中</span>{/if}
          </div>
          <div class="pes">
            {#each m.pes as p}
              <span class="pe" class:sel={m.focus && p.p === app.peIndex}>
                <i>P{p.p}</i>
                {#if p.s}<code>{p.s.outFirst || '—'}</code>{:else}<code class="dim">—</code>{/if}
              </span>
            {/each}
          </div>
          <div class="mau">MAU</div>
        </button>
      {/each}
    </div>

    <aside class="side">
      <h4>L1BM（この L1B 共有・現在行）</h4>
      <div class="l1bm">
        {#each l1bm as row}
          <div class="lrow" class:touched={row.touched}>
            <span class="addr">[{row.addr}]</span>
            <code>{format(row.words, app.view).join(' ')}</code>
          </div>
        {/each}
      </div>
      <p class="hint">MAB をクリックすると、その MAB の4 PEを記録し直します。</p>
      <div class="legend">
        {#each Object.entries(CATEGORY_COLORS) as [c, col]}
          <span><i style:background={col}></i>{c === 'offchip' ? 'DRAM/PDM' : c === 'l2' ? 'L2BM' : c === 'l1' ? 'L1BM' : 'PE'}</span>
        {/each}
      </div>
    </aside>
  </div>
</section>

<style>
  .l1bview {
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
  .main {
    flex: 1;
    min-height: 0;
    display: grid;
    grid-template-columns: minmax(0, 1fr) 240px;
    gap: 8px;
  }
  .grid {
    display: grid;
    grid-template-columns: repeat(4, minmax(0, 1fr));
    grid-template-rows: repeat(4, minmax(0, 1fr));
    gap: 5px;
    min-height: 0;
  }
  .mab {
    display: flex;
    flex-direction: column;
    min-width: 0;
    min-height: 0;
    padding: 3px 5px;
    text-align: left;
    background: var(--panel-2);
    border: 1px solid var(--line);
    border-radius: 4px;
    gap: 2px;
  }
  .mab:hover {
    border-color: var(--accent);
  }
  .mab.focus {
    border-color: var(--accent);
    box-shadow: inset 3px 0 var(--accent);
    background: color-mix(in srgb, var(--accent) 9%, var(--panel-2));
  }
  .mhead {
    display: flex;
    justify-content: space-between;
    align-items: baseline;
  }
  .mhead b {
    font-family: var(--mono);
    font-size: 10px;
  }
  .badge {
    font-size: 8px;
    color: var(--accent);
  }
  .pes {
    display: grid;
    grid-template-columns: 1fr 1fr;
    gap: 1px 4px;
    flex: 1;
  }
  .pe {
    display: flex;
    align-items: baseline;
    gap: 3px;
    min-width: 0;
    font-family: var(--mono);
    font-size: 9px;
  }
  .pe i {
    color: var(--muted);
    font-style: normal;
    font-size: 8px;
  }
  .pe code {
    white-space: nowrap;
    overflow: hidden;
    text-overflow: ellipsis;
  }
  .pe.sel {
    color: var(--accent);
    font-weight: 700;
  }
  .pe code.dim {
    color: var(--muted);
  }
  .mau {
    font-size: 7px;
    color: var(--muted);
    border-top: 1px solid var(--line);
    padding-top: 1px;
  }
  .side {
    display: flex;
    flex-direction: column;
    gap: 4px;
    min-height: 0;
    overflow: auto;
  }
  h4 {
    margin: 0;
    font-size: 10px;
    color: var(--muted);
    letter-spacing: 0.04em;
  }
  .l1bm {
    display: flex;
    flex-direction: column;
    gap: 1px;
  }
  .lrow {
    display: flex;
    justify-content: space-between;
    gap: 8px;
    padding: 1px 3px;
    font-family: var(--mono);
    font-size: 10px;
    border-radius: 2px;
  }
  .lrow.touched {
    background: color-mix(in srgb, var(--c-l1) 18%, transparent);
  }
  .addr {
    color: var(--muted);
  }
  .hint {
    color: var(--muted);
    font-size: 10px;
    margin: 4px 0;
    line-height: 1.4;
  }
  .legend {
    display: flex;
    flex-wrap: wrap;
    gap: 3px 8px;
    font-size: 9px;
    color: var(--muted);
  }
  .legend i {
    display: inline-block;
    width: 6px;
    height: 6px;
    border-radius: 1px;
    margin-right: 2px;
  }
  .muted {
    color: var(--muted);
  }
</style>
