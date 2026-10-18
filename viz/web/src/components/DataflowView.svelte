<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { player } from '../lib/player.svelte';
  import Datapath from './Datapath.svelte';
  import MabView from './MabView.svelte';
  import L1bView from './L1bView.svelte';
  import GroupView from './GroupView.svelte';
  import ChipSummary from './ChipSummary.svelte';
  import StepDiff from './StepDiff.svelte';
  import type { ScopeLevel } from '../lib/hierarchy';

  const trace = $derived(app.trace);
  let pinnedCycle = $state<number | null>(null);
  const cycle = $derived(player.playing || player.progress < 1 ? player.cycle : pinnedCycle);

  /** The last line that actually occupies steps; nops keep the previous scope. */
  const lastActive = $derived.by(() => {
    const lines = trace?.lines ?? [];
    for (let i = app.line; i >= 0; i--) {
      const l = lines[i];
      if (l && l.words > 0 && l.kind !== 'nop') return l;
    }
    return undefined;
  });

  const autoLevel = $derived<ScopeLevel>(
    !lastActive ? 'chip' : lastActive.kind === 'pe' ? 'pe' : 'chip',
  );
  const level = $derived<ScopeLevel>(app.autoFollow ? autoLevel : app.scope);

  const SCOPES: { id: ScopeLevel; label: string }[] = [
    { id: 'chip', label: '全体' },
    { id: 'group', label: 'Group' },
    { id: 'l1b', label: 'L1B' },
    { id: 'mab', label: 'MAB' },
    { id: 'pe', label: 'PE' },
  ];

  function choose(id: ScopeLevel) {
    app.setScope(id);
  }
</script>

<section class="df">
  <header>
    <nav class="crumbs" aria-label="階層">
      <button class:on={level === 'chip'} onclick={() => choose('chip')}>チップ</button>
      <span>/</span>
      <button class:on={level === 'group'} onclick={() => app.selectGroup(app.focusGroup)}>Group {app.focusGroup}</button>
      <span>/</span>
      <span class="plain">L2B {app.focusL2b}</span>
      <span>/</span>
      <button class:on={level === 'l1b'} onclick={() => app.selectL1b(app.focusL1b)}>L1B {app.focusL1b}</button>
      <span>/</span>
      <button class:on={level === 'mab'} onclick={() => app.selectMab(app.focusMab)}>MAB {app.focusMab}</button>
      <span>/</span>
      <button class:on={level === 'pe'} onclick={() => app.selectPe(app.peIndex)}>PE {app.pe}</button>
    </nav>

    <div class="scopes">
      {#each SCOPES as s}
        <button class:on={level === s.id} onclick={() => choose(s.id)}>{s.label}</button>
      {/each}
    </div>

    <button class="follow" class:on={app.autoFollow} onclick={() => (app.autoFollow ? (app.autoFollow = false) : app.followCurrent())}>
      {app.autoFollow ? '● 追従中' : '○ 手動'}
    </button>

    <span class="cycle">CYCLE {player.progress >= 1 ? '—' : player.cycle}</span>

    <select bind:value={app.view} title="値の表示形式">
      <option value="f32">単精度</option>
      <option value="f64">倍精度</option>
      <option value="f16">半精度 (1/6/9)</option>
      <option value="i32">整数</option>
      <option value="hex">16進</option>
    </select>
  </header>

  {#if level === 'pe'}
    <div class="toolbar">
      <span class="k">PE</span>
      {#each trace?.focus ?? [] as p, i}
        <button class:on={i === app.peIndex} onclick={() => app.setPeIndex(i)}>PE{p % 4}</button>
      {/each}
      <span class="sep">|</span>
      <span class="k">サイクル</span>
      <button class:on={cycle === null} onclick={() => { player.pause(); player.progress = 1; pinnedCycle = null; }}>全</button>
      {#each [0, 1, 2, 3] as c}
        <button class:on={cycle === c} onclick={() => { player.setCycle(c); pinnedCycle = c; }}>{c}</button>
      {/each}
      <span class="k">MAB {app.focusMab} / L1B {app.focusL1b}</span>
    </div>
  {/if}

  <div class="body">
    {#if level === 'pe'}
      <Datapath chrome={false} cycle={cycle} />
    {:else if level === 'mab'}
      <MabView />
    {:else if level === 'l1b'}
      <L1bView />
    {:else if level === 'group'}
      <GroupView />
    {:else}
      <ChipSummary />
    {/if}
  </div>

  {#if level === 'pe' || level === 'mab'}
    <StepDiff />
  {/if}
</section>

<style>
  .df {
    display: flex;
    flex-direction: column;
    min-height: 0;
    min-width: 0;
    background: var(--bg);
  }
  header {
    display: flex;
    align-items: center;
    gap: 8px;
    padding: 3px 8px;
    border-bottom: 1px solid var(--line);
    background: var(--panel);
    flex: none;
    flex-wrap: wrap;
  }
  .crumbs {
    display: flex;
    align-items: center;
    gap: 2px;
    font-family: var(--mono);
    font-size: 11px;
    min-width: 0;
  }
  .crumbs button {
    padding: 1px 5px;
    font-family: var(--mono);
    font-size: 11px;
  }
  .crumbs button.on {
    border-color: var(--accent);
    color: var(--accent);
    background: color-mix(in srgb, var(--accent) 12%, var(--panel));
  }
  .crumbs span {
    color: var(--muted);
  }
  .plain {
    white-space: nowrap;
  }
  .scopes {
    display: flex;
    gap: 2px;
    margin-left: auto;
  }
  .scopes button {
    font-size: 10px;
    padding: 1px 6px;
  }
  .scopes button.on {
    background: var(--accent);
    color: var(--bg);
  }
  .follow {
    font-size: 10px;
    padding: 1px 6px;
  }
  .follow.on {
    color: var(--good);
    border-color: color-mix(in srgb, var(--good) 50%, var(--line));
  }
  .cycle {
    font-family: var(--mono);
    font-size: 10px;
    color: var(--muted);
    white-space: nowrap;
  }
  select {
    font-size: 10px;
    padding: 0 4px;
  }
  .toolbar {
    display: flex;
    align-items: center;
    gap: 3px;
    padding: 2px 8px;
    border-bottom: 1px solid var(--line);
    background: var(--panel);
    flex: none;
    font-size: 10px;
  }
  .toolbar button {
    padding: 1px 6px;
    font-size: 10px;
  }
  .toolbar button.on {
    background: var(--accent);
    color: var(--bg);
  }
  .toolbar .k {
    color: var(--muted);
    margin: 0 3px;
    font-size: 9px;
    letter-spacing: 0.04em;
  }
  .toolbar .sep {
    color: var(--line);
    margin: 0 4px;
  }
  .body {
    flex: 1;
    min-height: 0;
    display: flex;
  }
  .body > :global(*) {
    flex: 1;
    min-height: 0;
  }
</style>
