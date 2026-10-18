<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { read } from '../lib/memory';
  import { format } from '../lib/numbers';
  import { locName } from '../lib/hierarchy';

  const line = $derived(app.trace?.lines[app.line]);

  interface Change {
    key: string;
    loc: string;
    addr: number;
    old: string;
    now: string;
    delta: number | null;
    cycle: number;
  }

  /** Writes of the focus PE in this line, compared with the state before the line. */
  const changes = $derived.by<Change[]>(() => {
    const map = new Map<string, Change>();
    for (const a of line?.accesses ?? []) {
      if (!a.write || a.loc === 'out' || a.unit !== app.pe || a.addr === null) continue;
      const per = a.loc === 't' ? 4 : 1;
      const base = a.addr * per;
      const n = Math.max(1, a.words.length);
      const key = `${a.loc}:${a.addr}`;
      const unit = `pe:${a.unit}`;
      const oldWords = Array.from({ length: n }, (_, i) => read(app.before, unit, a.loc, base + i) ?? 0);
      const newWords = Array.from({ length: n }, (_, i) => read(app.after, unit, a.loc, base + i) ?? 0);
      if (oldWords.every((v, i) => v === newWords[i])) continue;
      const oldText = format(oldWords, app.view).join(' ');
      const newText = format(newWords, app.view).join(' ');
      const oldN = Number(format(oldWords, app.view)[0]?.replace('−', '-'));
      const newN = Number(format(newWords, app.view)[0]?.replace('−', '-'));
      const delta = Number.isFinite(oldN) && Number.isFinite(newN) ? newN - oldN : null;
      map.set(key, {
        key,
        loc: a.loc,
        addr: a.addr,
        old: oldText,
        now: newText,
        delta,
        cycle: a.cycle,
      });
    }
    return [...map.values()];
  });
</script>

<section class="diff">
  <h4>この行の変更（前 → 後）</h4>
  {#if changes.length}
    <div class="rows">
      {#each changes.slice(0, 8) as c (c.key)}
        <div class="row">
          <span class="loc">{locName(c.loc)}[{c.addr}]</span>
          <span class="cycle">c{c.cycle}</span>
          <span class="old">{c.old}</span>
          <span class="arrow">→</span>
          <span class="now">{c.now}</span>
          {#if c.delta !== null && c.delta !== 0}
            <span class="delta" class:pos={c.delta > 0} class:neg={c.delta < 0}>
              {c.delta > 0 ? '+' : ''}{Number(c.delta.toPrecision(4))}
            </span>
          {/if}
        </div>
      {/each}
      {#if changes.length > 8}<span class="more">他 {changes.length - 8} 件</span>{/if}
    </div>
  {:else}
    <p class="none">この行は PE のメモリ値を書き換えません。</p>
  {/if}
</section>

<style>
  .diff {
    border-top: 1px solid var(--line);
    padding: 4px 10px 6px;
    background: var(--panel);
  }
  h4 {
    margin: 0 0 3px;
    font-size: 10px;
    letter-spacing: 0.04em;
    color: var(--muted);
    font-weight: 600;
  }
  .rows {
    display: flex;
    gap: 12px;
    overflow-x: auto;
    padding-bottom: 2px;
  }
  .row {
    display: flex;
    align-items: baseline;
    gap: 4px;
    font-family: var(--mono);
    font-size: 11px;
    white-space: nowrap;
  }
  .loc {
    color: var(--fg);
  }
  .cycle {
    color: var(--muted);
    font-size: 9px;
  }
  .old {
    color: var(--muted);
  }
  .arrow {
    color: var(--muted);
  }
  .now {
    color: var(--c-compute);
    font-weight: 600;
  }
  .delta {
    font-size: 10px;
    color: var(--muted);
  }
  .delta.pos {
    color: var(--good);
  }
  .delta.neg {
    color: var(--bad);
  }
  .more,
  .none {
    color: var(--muted);
    font-size: 10px;
    margin: 0;
    white-space: nowrap;
  }
</style>
