<script lang="ts">
  import { onMount } from 'svelte';
  import { app } from './lib/state.svelte';
  import SourceView from './components/SourceView.svelte';
  import ChipView from './components/ChipView.svelte';
  import Datapath from './components/Datapath.svelte';
  import Inspector from './components/Inspector.svelte';
  import Timeline from './components/Timeline.svelte';
  import Story from './components/Story.svelte';
  import Occupancy from './components/Occupancy.svelte';

  let mode = $state<'explorer' | 'story'>('explorer');
  let lower = $state<'pe' | 'occupancy'>('pe');
  let editing = $state(false);
  let draft = $state('');

  onMount(async () => {
    await app.init();
    const fromHash = decodeURIComponent(location.hash.slice(1));
    const first = app.problems.find((p) => p.name === fromHash) ?? app.problems.find((p) => p.name.startsWith('3.')) ?? app.problems[0];
    if (first) await app.open(first.name);
  });

  async function choose(name: string) {
    location.hash = encodeURIComponent(name);
    app.selection = null;
    app.line = 0;
    await app.open(name);
  }

  async function applyDraft() {
    app.solution = draft;
    editing = false;
    app.line = 0;
    await app.simulate();
  }

  async function onDrop(ev: DragEvent) {
    ev.preventDefault();
    const f = ev.dataTransfer?.files[0];
    if (!f) return;
    const text = await f.text();
    // A testcase contains the insertion marker; anything else is taken as a solution.
    if (text.includes('YOUR VSM WILL BE INSERTED HERE')) app.testcase = text;
    else app.solution = text;
    app.line = 0;
    await app.simulate();
  }
</script>

<div class="app" role="application" ondragover={(e) => e.preventDefault()} ondrop={onDrop}>
  <header class="top">
    <h1>MN-Core 2 データ移動ビジュアライザ</h1>
    <nav>
      <button class:on={mode === 'explorer'} onclick={() => (mode = 'explorer')}>Explorer</button>
      <button class:on={mode === 'story'} onclick={() => (mode = 'story')}>Story</button>
    </nav>
    {#if mode === 'explorer'}
      <select value={app.problem} onchange={(e) => choose((e.currentTarget as HTMLSelectElement).value)}>
        {#each app.problems as p}
          <option value={p.name}>{p.number}. {p.title}</option>
        {/each}
      </select>
      <button onclick={() => { draft = app.solution; editing = !editing; }}>{editing ? '閉じる' : 'VSM を編集'}</button>
      <span class="hint">VSM / testcase.vsm をドロップしても読み込めます</span>
    {/if}
    {#if app.loading}<span class="busy">シミュレーション中…</span>{/if}
    {#if app.error}<span class="err" title={app.error}>⚠ {app.error.slice(0, 80)}</span>{/if}
  </header>

  {#if mode === 'story'}
    <Story />
  {:else}
    {#if editing}
      <div class="editor">
        <textarea bind:value={draft} spellcheck="false"></textarea>
        <button onclick={applyDraft}>この VSM でシミュレーション</button>
      </div>
    {/if}
    <main class="explorer">
      <div class="left panel"><SourceView /></div>
      <div class="center">
        <div class="panel chipwrap"><ChipView /></div>
        <div class="panel pewrap">
          <div class="tabs">
            <button class:on={lower === 'pe'} onclick={() => (lower = 'pe')}>PE データパス</button>
            <button class:on={lower === 'occupancy'} onclick={() => (lower = 'occupancy')}>命令グループ占有</button>
          </div>
          {#if lower === 'pe'}<Datapath />{:else}<Occupancy />{/if}
        </div>
      </div>
      <div class="right panel"><Inspector /></div>
    </main>
    <Timeline />
  {/if}
</div>

<style>
  .app {
    display: flex;
    flex-direction: column;
    height: 100vh;
  }
  .top {
    display: flex;
    align-items: center;
    gap: 10px;
    padding: 6px 12px;
    border-bottom: 1px solid var(--line);
    font-size: 13px;
  }
  h1 {
    font-size: 14px;
    margin: 0 8px 0 0;
  }
  nav button.on {
    background: var(--accent);
    color: var(--bg);
  }
  .hint {
    color: var(--muted);
    font-size: 11px;
  }
  .busy {
    color: var(--accent);
  }
  .err {
    color: var(--bad);
    overflow: hidden;
    white-space: nowrap;
    text-overflow: ellipsis;
    max-width: 40vw;
  }
  .editor {
    display: flex;
    gap: 8px;
    padding: 6px 12px;
    border-bottom: 1px solid var(--line);
  }
  .editor textarea {
    flex: 1;
    height: 180px;
    font-family: var(--mono);
    font-size: 12px;
  }
  .explorer {
    flex: 1;
    min-height: 0;
    display: grid;
    grid-template-columns: minmax(240px, 22%) 1fr minmax(260px, 22%);
  }
  .panel {
    min-height: 0;
    min-width: 0;
    display: flex;
    flex-direction: column;
  }
  .left {
    border-right: 1px solid var(--line);
  }
  .right {
    border-left: 1px solid var(--line);
  }
  .center {
    min-width: 0;
    display: grid;
    grid-template-rows: minmax(0, 0.36fr) minmax(0, 0.64fr);
    min-height: 0;
  }
  .tabs {
    display: flex;
    gap: 4px;
    padding: 4px 8px 0;
    flex: none !important;
  }
  .tabs button.on {
    background: var(--accent);
    color: var(--bg);
  }
  .chipwrap {
    border-bottom: 1px solid var(--line);
  }
  .chipwrap > :global(*),
  .pewrap > :global(section) {
    flex: 1;
  }
</style>
