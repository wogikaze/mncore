<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { player } from '../lib/player.svelte';
  import type { Hazard } from '../lib/types';

  let list: HTMLOListElement | undefined = $state();

  const trace = $derived(app.trace);
  // Hazard reasons of each nop line, and which lines they connect.
  const nopInfo = $derived.by(() => {
    const m = new Map<number, Hazard[]>();
    if (!trace) return m;
    for (const n of trace.nops) m.set(n.line, n.needed_by.map((i) => trace.hazards[i]));
    return m;
  });
  const current = $derived(trace?.lines[app.line]);
  // Lines linked to the selected nop: the write and the read it separates.
  const linked = $derived.by(() => {
    const s = new Set<number>();
    for (const h of nopInfo.get(app.line) ?? []) {
      s.add(h.from);
      s.add(h.to);
    }
    return s;
  });

  $effect(() => {
    const el = list?.querySelector<HTMLElement>(`[data-i="${app.line}"]`);
    el?.scrollIntoView({ block: 'nearest' });
  });

  function reason(h: Hazard): string {
    const l = trace!.lines;
    const what = h.kind === 'data race' ? `${h.res}${h.addr !== null ? ` @${h.addr}` : ''} の書き込み→読み出し` : `${h.res} のポート`;
    return `${h.rule} ${h.kind === 'data race' ? 'データ競合' : 'ポート衝突'}: ${what}（${l[h.from].lineno}行→${l[h.to].lineno}行、${h.distance}/${h.required}サイクル）`;
  }
</script>

<section class="source">
  <header>
    <span>VSM</span>
    {#if trace}
      <span class="score" title="公式スコア = 命令語数（j + m）">score {trace.score}</span>
    {/if}
  </header>
  {#if trace}
    <ol bind:this={list}>
      {#each trace.lines as l, i}
        {@const reasons = nopInfo.get(i)}
        <li
          data-i={i}
          class:current={i === app.line}
          class:linked={linked.has(i)}
          class:nop={l.kind === 'nop'}
          class:dim={l.words === 0}
          class:err={trace.error_line === i}
        >
          <button onclick={() => { player.pause(); player.goto(i); }} title={reasons ? (reasons.length ? reasons.map(reason).join('\n') : 'どの規則にも必要とされていない（1ステップ削れる候補）') : ''}>
            <span class="step">{l.words ? l.step : ''}</span>
            <span class="text">{l.text}</span>
            {#if reasons}
              <span class="badge" class:removable={reasons.length === 0}>{reasons.length ? `必要 ×${reasons.length}` : '削れる候補'}</span>
            {/if}
          </button>
        </li>
      {/each}
    </ol>
    {#if current?.kind === 'nop' && nopInfo.get(app.line)?.length}
      <footer>
        <strong>この nop が必要な理由</strong>
        <ul>
          {#each nopInfo.get(app.line) ?? [] as h}
            <li>{reason(h)}</li>
          {/each}
        </ul>
      </footer>
    {/if}
  {/if}
</section>

<style>
  .source {
    display: flex;
    flex-direction: column;
    min-height: 0;
    font-family: var(--mono);
    font-size: 12px;
  }
  header {
    display: flex;
    justify-content: space-between;
    padding: 6px 8px;
    border-bottom: 1px solid var(--line);
    color: var(--muted);
  }
  .score {
    color: var(--accent);
    font-weight: 600;
  }
  ol {
    list-style: none;
    margin: 0;
    padding: 0;
    overflow: auto;
    flex: 1;
  }
  li button {
    all: unset;
    box-sizing: border-box;
    display: grid;
    grid-template-columns: 3.5em 1fr auto;
    gap: 6px;
    width: 100%;
    padding: 1px 8px;
    cursor: pointer;
    white-space: pre;
  }
  li:hover button {
    background: var(--hover);
  }
  .step {
    color: var(--muted);
    text-align: right;
  }
  .text {
    overflow: hidden;
    text-overflow: ellipsis;
  }
  .dim .text {
    color: var(--muted);
  }
  .nop .text {
    color: var(--warn);
  }
  .current button {
    background: var(--sel) !important;
  }
  .linked button {
    box-shadow: inset 3px 0 var(--warn);
  }
  .err button {
    box-shadow: inset 3px 0 var(--bad);
  }
  .badge {
    font-size: 10px;
    padding: 0 4px;
    border-radius: 3px;
    background: var(--warn-bg);
    color: var(--warn);
  }
  .badge.removable {
    background: var(--good-bg);
    color: var(--good);
  }
  footer {
    border-top: 1px solid var(--line);
    padding: 6px 8px;
    max-height: 30%;
    overflow: auto;
    font-family: var(--sans);
  }
  footer ul {
    margin: 4px 0 0;
    padding-left: 16px;
  }
</style>
