<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { player } from '../lib/player.svelte';
  import { activityOf } from '../lib/hierarchy';
  import { CATEGORY_COLORS, CATEGORY_NAMES } from '../lib/flows';

  const trace = $derived(app.trace);
  const line = $derived(trace?.lines[app.line]);
  const act = $derived(activityOf(line?.flows ?? []));
  const cycle = $derived(player.progress >= 1 ? null : player.cycle);
  const unitNames: Record<string, string> = {
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
  const units = $derived([...new Set((line?.exprs ?? []).map((e) => e.unit))]);
</script>

<section class="now" aria-label="現在の命令">
  <div class="clock">
    <div>
      <span class="k">STEP</span>
      <b>{line?.step ?? 0}</b>
      <span class="of">/ {trace?.score ?? 0}</span>
    </div>
    <div>
      <span class="k">CYCLE</span>
      <b>{cycle === null ? '—' : cycle}</b>
      <span class="of">/ 3</span>
    </div>
  </div>

  <div class="instr">
    <div class="ln">
      {#if line}<span>{line.lineno}行目</span>{/if}
      <span class="kind {line?.kind ?? ''}">{line?.kind === 'nop' ? 'NOP' : line?.kind === 'mv' ? 'MV' : line?.kind === 'pe' ? 'PE 命令' : line?.kind ?? ''}</span>
      {#each units as u}
        <span class="unit">{unitNames[u] ?? u}</span>
      {/each}
    </div>
    <code title={line?.text}>{line?.text ?? '—'}</code>
  </div>

  <div class="where">
    <span class="k">選択位置</span>
    <button onclick={() => app.selectGroup(app.focusGroup)} class:on={app.scope === 'group'}>G{app.focusGroup}</button>
    <span class="sep">/</span><span class="plain">L2B {app.focusL2b}</span><span class="sep">/</span>
    <button onclick={() => app.selectL1b(app.focusL1b)} class:on={app.scope === 'l1b'}>L1B {app.focusL1b}</button>
    <button onclick={() => app.selectMab(app.focusMab)} class:on={app.scope === 'mab'}>MAB {app.focusMab}</button>
    <button onclick={() => app.selectPe(app.peIndex)} class:on={app.scope === 'pe'}>PE {app.pe}</button>
  </div>

  <div class="status">
    {#if act.cats.size}
      <span class="cats">
        {#each [...act.cats] as c}
          <i style:background={CATEGORY_COLORS[c]}></i>{CATEGORY_NAMES[c]}
        {/each}
      </span>
    {/if}
    {#if trace?.output.values}
      <span class:good={trace.output.failures === 0} class:bad={trace.output.failures > 0}>
        {trace.output.failures === 0 ? '出力 OK' : `誤差 ${trace.output.failures}`}
      </span>
    {/if}
  </div>
</section>

<style>
  .now {
    display: grid;
    grid-template-columns: auto minmax(0, 1fr) auto auto;
    align-items: center;
    gap: 16px;
    min-height: 52px;
    padding: 6px 14px;
    background: var(--panel);
    border-bottom: 1px solid var(--line);
  }
  .clock {
    display: flex;
    gap: 14px;
    font-family: var(--mono);
    font-size: 12px;
  }
  .clock > div {
    display: flex;
    align-items: baseline;
    gap: 4px;
  }
  .clock b {
    font-size: 20px;
    line-height: 1;
    color: var(--fg);
  }
  .k {
    color: var(--muted);
    font-size: 10px;
    letter-spacing: 0.08em;
  }
  .of {
    color: var(--muted);
    font-size: 10px;
  }
  .instr {
    min-width: 0;
    display: flex;
    flex-direction: column;
    gap: 2px;
  }
  .ln {
    display: flex;
    align-items: center;
    gap: 6px;
    font-size: 11px;
    color: var(--muted);
    min-width: 0;
  }
  .ln > span:first-child {
    font-family: var(--mono);
    color: var(--fg);
    font-weight: 600;
  }
  .kind {
    font-size: 9px;
    text-transform: uppercase;
    letter-spacing: 0.06em;
    padding: 0 4px;
    border: 1px solid var(--line);
    border-radius: 3px;
  }
  .kind.mv {
    color: var(--c-offchip);
    border-color: color-mix(in srgb, var(--c-offchip) 50%, var(--line));
  }
  .kind.nop {
    color: var(--warn);
    border-color: color-mix(in srgb, var(--warn) 50%, var(--line));
  }
  .unit {
    font-size: 10px;
    padding: 0 4px;
    border-radius: 3px;
    background: var(--panel-2);
    color: var(--fg);
  }
  code {
    font-family: var(--mono);
    font-size: 14px;
    font-weight: 600;
    white-space: nowrap;
    overflow: hidden;
    text-overflow: ellipsis;
  }
  .where {
    display: flex;
    align-items: center;
    gap: 3px;
    font-family: var(--mono);
    font-size: 11px;
    white-space: nowrap;
  }
  .where button {
    padding: 1px 5px;
    font-family: var(--mono);
    font-size: 11px;
  }
  .sep,
  .plain {
    color: var(--muted);
  }
  .where button.on {
    border-color: var(--accent);
    color: var(--accent);
    background: color-mix(in srgb, var(--accent) 14%, var(--panel));
  }
  .status {
    display: flex;
    flex-direction: column;
    align-items: flex-end;
    gap: 2px;
    font-size: 10px;
    white-space: nowrap;
  }
  .cats {
    display: flex;
    gap: 3px;
    align-items: center;
    color: var(--muted);
  }
  .cats i {
    display: inline-block;
    width: 7px;
    height: 7px;
    border-radius: 2px;
    margin-left: 2px;
  }
  .good {
    color: var(--good);
  }
  .bad {
    color: var(--bad);
  }
</style>
