<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { peSummary, type PeSummary, type ValueRow } from '../lib/hierarchy';
  import { format } from '../lib/numbers';
  import { locLabel } from '../lib/hierarchy';

  const trace = $derived(app.trace);
  const line = $derived(trace?.lines[app.line]);
  const mab = $derived(app.focusMab);
  const base = $derived(mab * 4);
  const pes = $derived([0, 1, 2, 3].map((i) => ({ i, pe: base + i, s: peSummary(line, base + i, app.view) })));

  const UNIT_NAME: Record<string, string> = {
    alu: 'ALU',
    mau: 'MAU',
    matrix: 'MAU 行列',
    mwrite: '行列書込',
    mread: '行列読出',
    'l1-to-pe': 'L1BM→PE',
    'pe-to-l1': 'PE→L1BM',
    l2: 'L2BM',
    wait: 'wait',
    noforward: 'noforward',
    other: 'その他',
  };

  function vrow(r: ValueRow): string {
    return `${locLabel(r.loc, r.addr)} = ${format(r.words, app.view).join(' ')}`;
  }

  function open(i: number, s: PeSummary) {
    app.selectPe(i);
    app.detailTab = 'values';
    if (s.dest) app.selection = { unit: base + i, loc: s.dest.loc, addr: s.dest.addr, line: app.line };
  }
</script>

<section class="mabview">
  <header>
    <div>
      <h3>MAB {mab}</h3>
      <span class="sub">Group {app.focusGroup} / L2B {app.focusL2b} / L1B {app.focusL1b}・{line?.lineno}行目</span>
    </div>
    <p class="hint">PE をクリックすると、その1 PEのデータフローを開きます。</p>
  </header>

  {#if line?.exprs.length}
    <div class="grid">
      {#each pes as p (p.pe)}
        <button class="card" class:sel={p.i === app.peIndex} onclick={() => open(p.i, p.s)}>
          <div class="head">
            <b>PE {p.pe}</b>
            <span class="counts">読 {p.s.readCount}・書 {p.s.writeCount}</span>
          </div>
          <div class="flow">
            <div class="block">
              <span class="blabel">読</span>
              <div class="vals">
                {#each p.s.reads.slice(0, 2) as r}
                  <div class="val" title={vrow(r)}>{vrow(r)}</div>
                {:else}
                  <div class="empty">なし</div>
                {/each}
                {#if p.s.reads.length > 2}<div class="more">+{p.s.reads.length - 2}</div>{/if}
              </div>
            </div>
            <div class="unitrow">
              <span class="arrow">↓</span>
              {#each line.exprs as e}
                <span class="op">{UNIT_NAME[e.unit] ?? e.unit}</span>
                <code>{e.opcode}</code>
              {/each}
              <span class="arrow">↓</span>
            </div>
            <div class="block">
              <span class="blabel">書</span>
              <div class="vals">
                {#each p.s.writes.slice(0, 2) as w}
                  <div class="val" title={vrow(w)}>{vrow(w)}</div>
                {:else}
                  <div class="empty">なし</div>
                {/each}
                {#if p.s.writes.length > 2}<div class="more">+{p.s.writes.length - 2}</div>{/if}
              </div>
            </div>
          </div>
          <div class="result">
            <span class="k">結果</span>
            <code>{p.s.out || '—'}</code>
          </div>
        </button>
      {/each}
    </div>
  {:else}
    <div class="none">
      <b>この行は PE 命令ではありません。</b>
      <span>MV / nop の転送は「全体」または「Group」表示で確認できます。</span>
    </div>
  {/if}
</section>

<style>
  .mabview {
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
  }
  h3 {
    margin: 0;
    font-size: 15px;
  }
  .sub,
  .hint {
    color: var(--muted);
    font-size: 11px;
  }
  .hint {
    margin: 0 0 0 auto;
  }
  .grid {
    flex: 1;
    min-height: 0;
    display: grid;
    grid-template-columns: 1fr 1fr;
    grid-template-rows: 1fr 1fr;
    gap: 8px;
  }
  .card {
    display: flex;
    flex-direction: column;
    min-width: 0;
    min-height: 0;
    padding: 6px 8px;
    text-align: left;
    background: var(--panel-2);
    border: 1px solid var(--line);
    border-radius: 5px;
    gap: 4px;
    overflow: hidden;
  }
  .card:hover {
    border-color: var(--accent);
  }
  .card.sel {
    border-color: var(--accent);
    box-shadow: inset 3px 0 var(--accent);
  }
  .head {
    display: flex;
    align-items: baseline;
    justify-content: space-between;
    flex: none;
  }
  .head b {
    font-family: var(--mono);
    font-size: 13px;
  }
  .counts {
    color: var(--muted);
    font-size: 10px;
  }
  .flow {
    flex: 1;
    min-height: 0;
    display: flex;
    flex-direction: column;
    gap: 1px;
    overflow: hidden;
  }
  .block {
    display: grid;
    grid-template-columns: 18px minmax(0, 1fr);
    column-gap: 3px;
    align-items: start;
    min-width: 0;
    overflow: hidden;
    flex: none;
  }
  .blabel {
    font-size: 9px;
    color: var(--muted);
    line-height: 1.25;
    padding-top: 0;
  }
  .vals {
    display: flex;
    flex-direction: column;
    gap: 0;
    min-width: 0;
    overflow: hidden;
  }
  .val {
    font-family: var(--mono);
    font-size: 10px;
    line-height: 1.25;
    white-space: nowrap;
    overflow: hidden;
    text-overflow: ellipsis;
    max-width: 100%;
  }
  .empty,
  .more {
    color: var(--muted);
    font-size: 10px;
  }
  .unitrow {
    display: flex;
    align-items: center;
    justify-content: center;
    gap: 4px;
    min-height: 20px;
    border-top: 1px solid var(--line);
    border-bottom: 1px solid var(--line);
    padding: 1px 0;
  }
  .arrow {
    color: var(--muted);
    font-size: 11px;
  }
  .op {
    font-size: 9px;
    color: var(--fg);
    background: var(--panel);
    border: 1px solid var(--line);
    border-radius: 3px;
    padding: 0 3px;
    white-space: nowrap;
  }
  code {
    font-family: var(--mono);
    font-size: 10px;
    white-space: nowrap;
    overflow: hidden;
    text-overflow: ellipsis;
    max-width: 100%;
  }
  .result {
    flex: none;
    display: flex;
    gap: 6px;
    align-items: baseline;
    border-top: 1px solid var(--line);
    padding-top: 3px;
  }
  .k {
    color: var(--muted);
    font-size: 10px;
  }
  .result code {
    color: var(--accent);
    font-size: 11px;
  }
  .none {
    display: flex;
    flex-direction: column;
    gap: 4px;
    color: var(--muted);
    font-size: 12px;
    padding: 20px;
  }
  .none b {
    color: var(--fg);
    font-size: 14px;
  }
</style>
