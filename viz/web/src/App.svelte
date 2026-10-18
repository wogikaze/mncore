<script lang="ts">
  import { onMount } from 'svelte';
  import { app } from './lib/state.svelte';
  import NowBar from './components/NowBar.svelte';
  import SourceView from './components/SourceView.svelte';
  import OverviewMap from './components/OverviewMap.svelte';
  import DataflowView from './components/DataflowView.svelte';
  import ChipSummary from './components/ChipSummary.svelte';
  import Inspector from './components/Inspector.svelte';
  import MemoryView from './components/MemoryView.svelte';
  import Occupancy from './components/Occupancy.svelte';
  import Timeline from './components/Timeline.svelte';
  import Story from './components/Story.svelte';

  let mode = $state<'explorer' | 'story'>('explorer');
  let editing = $state(false);
  let draft = $state('');

  // Pane geometry. The defaults fit 1440x900 with enough room for the dataflow.
  let leftW = $state(300);
  let rightW = $state(380);
  let bottomH = $state(96);
  let overviewH = $state(210);
  let leftOpen = $state(true);
  let rightOpen = $state(true);
  let bottomOpen = $state(true);
  let overviewOpen = $state(true);
  let fullMap = $state(false);

  type DragKind = 'left' | 'right' | 'bottom' | 'overview';
  let drag = $state<{ kind: DragKind; start: number; size: number } | null>(null);

  let theme = $state<'dark' | 'light'>('dark');

  const clamp = (v: number, lo: number, hi: number) => Math.max(lo, Math.min(hi, v));

  function applyTheme(t: 'dark' | 'light') {
    theme = t;
    document.documentElement.dataset.theme = t;
    try {
      localStorage.setItem('mncore-theme', t);
    } catch {
      /* ignore */
    }
  }

  function saveLayout() {
    try {
      localStorage.setItem(
        'mncore-layout',
        JSON.stringify({ leftW, rightW, bottomH, overviewH, leftOpen, rightOpen, bottomOpen, overviewOpen }),
      );
    } catch {
      /* ignore */
    }
  }

  function startDrag(kind: DragKind, ev: PointerEvent) {
    ev.preventDefault();
    const size =
      kind === 'left' ? leftW : kind === 'right' ? rightW : kind === 'bottom' ? bottomH : overviewH;
    drag = { kind, start: kind === 'left' || kind === 'right' ? ev.clientX : ev.clientY, size };
    (ev.currentTarget as Element).setPointerCapture?.(ev.pointerId);
  }

  function moveDrag(ev: PointerEvent) {
    if (!drag) return;
    const d = drag;
    if (d.kind === 'left') {
      leftW = clamp(d.size + (ev.clientX - d.start), 220, Math.min(460, window.innerWidth - 560));
    } else if (d.kind === 'right') {
      rightW = clamp(d.size - (ev.clientX - d.start), 300, Math.min(560, window.innerWidth - 560));
    } else if (d.kind === 'bottom') {
      bottomH = clamp(d.size - (ev.clientY - d.start), 92, Math.min(280, window.innerHeight - 330));
    } else {
      overviewH = clamp(d.size + (ev.clientY - d.start), 120, Math.min(340, window.innerHeight - 400));
    }
  }

  function endDrag() {
    if (!drag) return;
    drag = null;
    saveLayout();
  }

  onMount(async () => {
    try {
      const t = localStorage.getItem('mncore-theme');
      applyTheme(t === 'light' ? 'light' : 'dark');
    } catch {
      applyTheme('dark');
    }
    try {
      const saved = localStorage.getItem('mncore-layout');
      if (saved) {
        const s = JSON.parse(saved);
        leftW = clamp(Number(s.leftW) || 300, 220, 460);
        rightW = clamp(Number(s.rightW) || 380, 300, 560);
        bottomH = clamp(Number(s.bottomH) || 96, 92, 280);
        overviewH = clamp(Number(s.overviewH) || 210, 120, 340);
        leftOpen = Boolean(s.leftOpen ?? true);
        rightOpen = Boolean(s.rightOpen ?? true);
        bottomOpen = Boolean(s.bottomOpen ?? true);
        overviewOpen = Boolean(s.overviewOpen ?? true);
      }
    } catch {
      /* ignore */
    }
    document.documentElement.dataset.theme = theme;
    await app.init();
    const fromHash = decodeURIComponent(location.hash.slice(1));
    const first =
      app.problems.find((p) => p.name === fromHash) ??
      app.problems.find((p) => p.name.startsWith('3.')) ??
      app.problems[0];
    if (first) await app.open(first.name);
  });

  async function choose(name: string) {
    location.hash = encodeURIComponent(name);
    app.selection = null;
    app.line = 0;
    fullMap = false;
    await app.open(name);
  }

  async function applyDraft() {
    app.solution = draft;
    editing = false;
    app.line = 0;
    fullMap = false;
    await app.simulate();
  }

  async function onDrop(ev: DragEvent) {
    ev.preventDefault();
    const f = ev.dataTransfer?.files[0];
    if (!f) return;
    const text = await f.text();
    if (text.includes('YOUR VSM WILL BE INSERTED HERE')) app.testcase = text;
    else app.solution = text;
    app.line = 0;
    fullMap = false;
    await app.simulate();
  }

  function toggleTheme() {
    applyTheme(theme === 'dark' ? 'light' : 'dark');
  }
</script>

<svelte:window onpointermove={moveDrag} onpointerup={endDrag} />

<div class="app" role="application" ondragover={(e) => e.preventDefault()} ondrop={onDrop}>
  <header class="top">
    <div class="brand">
      <span class="mark">MN</span>
      <div>
        <b>MN-Core 2</b>
        <small>Dataflow Explorer</small>
      </div>
    </div>

    <nav class="modes">
      <button class:on={mode === 'explorer'} onclick={() => (mode = 'explorer')}>Explorer</button>
      <button class:on={mode === 'story'} onclick={() => (mode = 'story')}>Story</button>
    </nav>

    {#if mode === 'explorer'}
      <select class="problem" value={app.problem} onchange={(e) => choose((e.currentTarget as HTMLSelectElement).value)}>
        {#each app.problems as p}
          <option value={p.name}>{p.number}. {p.title}</option>
        {/each}
      </select>
      <button onclick={() => { draft = app.solution; editing = !editing; }}>{editing ? '編集を閉じる' : 'VSM 編集'}</button>
      <span class="hint">VSM / testcase.vsm をドロップ</span>
    {/if}

    <div class="spacer"></div>
    {#if mode === 'explorer'}
      <div class="panes" aria-label="パネル表示">
        <button class:on={leftOpen} onclick={() => { leftOpen = !leftOpen; saveLayout(); }}>ソース</button>
        <button class:on={overviewOpen} onclick={() => { overviewOpen = !overviewOpen; saveLayout(); }}>概要</button>
        <button class:on={rightOpen} onclick={() => { rightOpen = !rightOpen; saveLayout(); }}>詳細</button>
        <button class:on={bottomOpen} onclick={() => { bottomOpen = !bottomOpen; saveLayout(); }}>時間</button>
      </div>
    {/if}
    <button class="theme" onclick={toggleTheme} title={theme === 'dark' ? 'ライトテーマ' : 'ダークテーマ'}>{theme === 'dark' ? '☀' : '☾'}</button>
    {#if app.loading}<span class="busy">実行中…</span>{/if}
    {#if app.error}<span class="err" title={app.error}>⚠ {app.error.slice(0, 80)}</span>{/if}
  </header>

  {#if mode === 'explorer'}
    <NowBar />
    {#if editing}
      <div class="editor">
        <textarea bind:value={draft} spellcheck="false"></textarea>
        <button onclick={applyDraft}>この VSM で実行</button>
      </div>
    {/if}

    <div class="workspace">
      <div class="mainrow">
        {#if leftOpen}
          <div class="left pane" style:width="{leftW}px">
            <SourceView />
          </div>
          <div class="vsplit" role="separator" aria-orientation="vertical" onpointerdown={(e) => startDrag('left', e)}></div>
        {/if}

        <div class="center">
          {#if fullMap}
            <div class="mapfull">
              <OverviewMap large onclose={() => (fullMap = false)} />
              <ChipSummary />
            </div>
          {:else}
            {#if overviewOpen}
              <div class="overview pane" style:height="{overviewH}px">
                <OverviewMap onfull={() => (fullMap = true)} />
              </div>
              <div class="hsplit" role="separator" aria-orientation="horizontal" onpointerdown={(e) => startDrag('overview', e)}></div>
            {/if}
            <div class="detail">
              <DataflowView />
            </div>
          {/if}
        </div>

        {#if rightOpen}
          <div class="vsplit" role="separator" aria-orientation="vertical" onpointerdown={(e) => startDrag('right', e)}></div>
          <div class="right pane" style:width="{rightW}px">
            <div class="righthead">
              <div class="tabs">
                <button class:on={app.detailTab === 'values'} onclick={() => (app.detailTab = 'values')}>値・競合</button>
                <button class:on={app.detailTab === 'memory'} onclick={() => (app.detailTab = 'memory')}>メモリ</button>
                <button class:on={app.detailTab === 'occupancy'} onclick={() => (app.detailTab = 'occupancy')}>占有</button>
              </div>
              <button class="collapse" title="詳細パネルを閉じる" onclick={() => { rightOpen = false; saveLayout(); }}>×</button>
            </div>
            <div class="rightbody">
              {#if app.detailTab === 'values'}<Inspector />{:else if app.detailTab === 'memory'}<MemoryView />{:else}<Occupancy />{/if}
            </div>
          </div>
        {/if}
      </div>

      {#if bottomOpen}
        <div class="hsplit full" role="separator" aria-orientation="horizontal" onpointerdown={(e) => startDrag('bottom', e)}></div>
        <div class="bottom pane" style:height="{bottomH}px">
          <Timeline />
        </div>
      {/if}
    </div>
  {:else}
    <Story />
  {/if}
</div>

<style>
  .app {
    display: flex;
    flex-direction: column;
    height: 100vh;
    overflow: hidden;
  }
  .top {
    display: flex;
    align-items: center;
    gap: 8px;
    min-height: 44px;
    padding: 0 12px;
    border-bottom: 1px solid var(--line);
    background: var(--panel);
    flex: none;
  }
  .brand {
    display: flex;
    align-items: center;
    gap: 8px;
    margin-right: 8px;
    white-space: nowrap;
  }
  .mark {
    display: grid;
    place-items: center;
    width: 26px;
    height: 26px;
    border-radius: 5px;
    background: var(--accent);
    color: var(--bg);
    font-family: var(--mono);
    font-size: 10px;
    font-weight: 700;
  }
  .brand b {
    display: block;
    font-size: 12px;
    line-height: 1.1;
  }
  .brand small {
    display: block;
    font-size: 9px;
    color: var(--muted);
    letter-spacing: 0.04em;
  }
  .modes {
    display: flex;
    gap: 2px;
  }
  .modes button {
    font-size: 11px;
    padding: 2px 8px;
  }
  .modes button.on {
    background: var(--accent);
    color: var(--bg);
  }
  .problem {
    max-width: 260px;
    font-size: 11px;
  }
  .hint {
    color: var(--muted);
    font-size: 10px;
    white-space: nowrap;
  }
  .spacer {
    flex: 1;
  }
  .panes {
    display: flex;
    gap: 1px;
  }
  .panes button {
    font-size: 10px;
    padding: 1px 5px;
    color: var(--muted);
  }
  .panes button.on {
    color: var(--fg);
    border-color: var(--accent);
    background: color-mix(in srgb, var(--accent) 10%, var(--panel));
  }
  .theme {
    width: 28px;
    height: 24px;
    padding: 0;
    font-size: 12px;
  }
  .busy {
    color: var(--accent);
    font-size: 10px;
  }
  .err {
    color: var(--bad);
    overflow: hidden;
    white-space: nowrap;
    text-overflow: ellipsis;
    max-width: 30vw;
    font-size: 10px;
  }
  @media (max-width: 1200px) {
    .hint {
      display: none;
    }
    .problem {
      max-width: 180px;
    }
  }
  .editor {
    display: flex;
    gap: 8px;
    padding: 6px 12px;
    border-bottom: 1px solid var(--line);
    background: var(--panel);
    flex: none;
  }
  .editor textarea {
    flex: 1;
    height: 150px;
    font-family: var(--mono);
    font-size: 11px;
  }
  .workspace {
    flex: 1;
    min-height: 0;
    display: flex;
    flex-direction: column;
    overflow: hidden;
  }
  .mainrow {
    flex: 1;
    min-height: 0;
    display: flex;
    min-width: 0;
  }
  .pane {
    min-height: 0;
    min-width: 0;
    display: flex;
    flex-direction: column;
    background: var(--panel);
    overflow: hidden;
  }
  .left {
    flex: none;
    border-right: 1px solid var(--line);
  }
  .left > :global(*) {
    flex: 1;
    min-height: 0;
  }
  .overview.pane > :global(*) {
    flex: 1;
    min-height: 0;
  }
  .bottom.pane > :global(*) {
    flex: 1;
    min-height: 0;
  }
  .right {
    flex: none;
    border-left: 1px solid var(--line);
  }
  .center {
    flex: 1;
    min-width: 0;
    min-height: 0;
    display: flex;
    flex-direction: column;
    background: var(--bg);
  }
  .overview {
    flex: none;
    border-bottom: 1px solid var(--line);
    background: var(--panel);
  }
  .detail {
    flex: 1;
    min-height: 0;
    min-width: 0;
    display: flex;
    background: var(--bg);
  }
  .mapfull {
    flex: 1;
    min-height: 0;
    min-width: 0;
    display: grid;
    grid-template-rows: minmax(240px, 0.56fr) minmax(0, 0.44fr);
    background: var(--panel);
  }
  .mapfull > :global(*) {
    min-height: 0;
  }
  .detail > :global(*) {
    flex: 1;
    min-height: 0;
  }
  .bottom {
    flex: none;
    background: var(--panel);
  }
  .vsplit {
    flex: none;
    width: 5px;
    cursor: col-resize;
    background: var(--line);
    opacity: 0.55;
  }
  .vsplit:hover {
    opacity: 1;
    background: var(--accent);
  }
  .hsplit {
    flex: none;
    height: 5px;
    cursor: row-resize;
    background: var(--line);
    opacity: 0.55;
  }
  .hsplit:hover {
    opacity: 1;
    background: var(--accent);
  }
  .hsplit.full {
    width: 100%;
  }
  .righthead {
    display: flex;
    align-items: center;
    gap: 4px;
    padding: 3px 6px;
    border-bottom: 1px solid var(--line);
    flex: none;
  }
  .tabs {
    display: flex;
    gap: 2px;
    flex: 1;
  }
  .tabs button {
    font-size: 10px;
    padding: 1px 6px;
  }
  .tabs button.on {
    background: var(--accent);
    color: var(--bg);
  }
  .collapse {
    width: 22px;
    height: 20px;
    padding: 0;
    font-size: 12px;
    color: var(--muted);
  }
  .rightbody {
    flex: 1;
    min-height: 0;
    display: flex;
    overflow: hidden;
  }
  .rightbody > :global(*) {
    flex: 1;
    min-width: 0;
    min-height: 0;
  }
</style>
