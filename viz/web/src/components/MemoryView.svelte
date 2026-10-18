<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { format, hex } from '../lib/numbers';
  import { read } from '../lib/memory';

  // Word memories of the selected PE after the current step. LM/GRF are shown per 64-bit
  // long word (the unit the hardware transfers); T is shown per cycle. Clicking a cell
  // selects it for the provenance panel, which makes arbitrary addresses inspectable.

  const LOCS = [
    { id: 'lm0', label: 'LM0 ($m)', words: 4096 },
    { id: 'lm1', label: 'LM1 ($n)', words: 4096 },
    { id: 'grf0', label: 'GRF0 ($r)', words: 512 },
    { id: 'grf1', label: 'GRF1 ($s)', words: 512 },
    { id: 't', label: 'T ($t)', words: 16 },
    { id: 'omr', label: 'マスク (OMR)', words: 16 },
  ] as const;
  type LocId = (typeof LOCS)[number]['id'];

  const PAGE = 64; // long words per page
  let loc = $state<LocId>('lm0');
  let page = $state(0);
  let jump = $state(0);

  const trace = $derived(app.trace);
  const line = $derived(trace?.lines[app.line]);
  const pe = $derived(app.pe);
  const info = $derived(LOCS.find((l) => l.id === loc) ?? LOCS[0]);
  const longWords = $derived(info.words / 2);
  const pages = $derived(loc === 't' || loc === 'omr' ? 1 : Math.max(1, Math.ceil(longWords / PAGE)));
  const pageStart = $derived(Math.min(Math.max(0, page), pages - 1) * PAGE);

  // A new PE or memory starts at its first page.
  $effect(() => {
    loc;
    pe;
    page = 0;
  });

  interface Cell {
    addr: number;
    words: number[];
  }

  const cells = $derived.by<Cell[]>(() => {
    if (loc === 't') return [];
    if (loc === 'omr') {
      return Array.from({ length: 16 }, (_, i) => ({
        addr: i,
        words: [read(app.after, `pe:${pe}`, 'omr', i) ?? 0],
      }));
    }
    const n = Math.min(PAGE, Math.max(0, longWords - pageStart));
    return Array.from({ length: n }, (_, i) => {
      const lw = pageStart + i;
      return {
        addr: lw * 2,
        words: [read(app.after, `pe:${pe}`, loc, lw * 2) ?? 0, read(app.after, `pe:${pe}`, loc, lw * 2 + 1) ?? 0],
      };
    });
  });

  const tCells = $derived.by<Cell[]>(() =>
    Array.from({ length: 4 }, (_, c) => ({
      addr: c,
      words: [0, 1, 2, 3].map((i) => read(app.after, `pe:${pe}`, 't', c * 4 + i) ?? 0),
    })),
  );

  /** Word addresses written by the current line (used to outline the cells). */
  const written = $derived.by(() => {
    const s = new Set<number>();
    for (const a of line?.accesses ?? []) {
      if (!a.write || a.unit !== pe || a.loc !== loc || a.addr === null) continue;
      const n = loc === 't' || loc === 'omr' ? 1 : Math.max(1, a.words.length);
      for (let k = 0; k < n; k++) s.add(a.addr + k);
    }
    return s;
  });

  function cellWritten(c: Cell, width: number): boolean {
    if (width === 1) return written.has(c.addr);
    return written.has(c.addr) || written.has(c.addr + 1);
  }

  function isSelected(addr: number, width: number): boolean {
    const s = app.selection;
    if (!s || s.unit !== pe || s.loc !== loc || s.addr === null || s.line !== app.line) return false;
    return s.addr >= addr && s.addr < addr + width;
  }

  function pick(addr: number) {
    app.selection = { unit: pe, loc, addr, line: app.line };
    app.detailTab = 'values';
  }

  function cellText(words: number[]): string {
    // OMR entries are one word; f64 cannot be formed from a single word.
    if (app.view === 'f64' && words.length < 2) return hex(words[0] ?? 0);
    return format(words, app.view).join(' ');
  }

  function jumpToWrite() {
    const a = (line?.accesses ?? []).find((x) => x.write && x.unit === pe && x.loc === loc && x.addr !== null);
    if (!a || a.addr === null) return;
    if (loc === 't' || loc === 'omr') return;
    page = Math.floor(Math.floor(a.addr / 2) / PAGE);
  }

  function doJump() {
    const n = Number(jump);
    if (!Number.isFinite(n) || n < 0) return;
    if (loc === 't') {
      app.selection = { unit: pe, loc, addr: Math.min(3, Math.trunc(n)), line: app.line };
    } else if (loc === 'omr') {
      app.selection = { unit: pe, loc, addr: Math.min(15, Math.trunc(n)), line: app.line };
    } else {
      const word = Math.min(info.words - 2, Math.trunc(n));
      page = Math.floor(Math.floor(word / 2) / PAGE);
      app.selection = { unit: pe, loc, addr: word - (word % 2), line: app.line };
    }
  }
</script>

<section class="mem">
  <header>
    <div class="tabs">
      {#each LOCS as m}
        <button class:on={loc === m.id} onclick={() => (loc = m.id)}>{m.label}</button>
      {/each}
    </div>
    <div class="tabs">
      {#each trace?.focus ?? [] as p, i}
        <button class:on={i === app.peIndex} onclick={() => app.setPeIndex(i)}>PE{p % 4}</button>
      {/each}
    </div>
    <span class="where">PE #{pe}・{line?.lineno}行目の後</span>
    <label>
      表示
      <select bind:value={app.view}>
        <option value="f32">単精度</option>
        <option value="f64">倍精度</option>
        <option value="f16">半精度 (1/6/9)</option>
        <option value="i32">整数</option>
        <option value="hex">16進</option>
      </select>
    </label>
    <button onclick={jumpToWrite} disabled={loc === 't' || loc === 'omr'}>現在行の書込みへ</button>
  </header>

  {#if pages > 1 || loc === 't' || loc === 'omr'}
    <div class="pager">
      {#if pages > 1}
        <button onclick={() => (page = Math.max(0, page - 1))} disabled={page <= 0}>前</button>
        <span>長語 {pageStart}–{Math.min(info.words, pageStart + PAGE) - 1}</span>
        <button onclick={() => (page = Math.min(pages - 1, page + 1))} disabled={page >= pages - 1}>次</button>
      {/if}
      <label>
        アドレス
        <input type="number" min="0" max={loc === 't' ? 3 : info.words - 1} bind:value={jump} onkeydown={(e) => e.key === 'Enter' && doJump()} />
      </label>
      <button onclick={doJump}>移動</button>
    </div>
  {/if}

  {#if loc === 't'}
    <div class="tgrid">
      {#each tCells as c}
        <button class="cell" class:written={cellWritten(c, 1)} class:sel={isSelected(c.addr, 1)} onclick={() => pick(c.addr)}>
          <span class="a">cycle {c.addr}（語 {c.addr * 4}–{c.addr * 4 + 3}）</span>
          <span class="v">{cellText(c.words)}</span>
        </button>
      {/each}
    </div>
  {:else if loc === 'omr'}
    <div class="grid omr">
      {#each cells as c}
        <button class="cell" class:written={cellWritten(c, 1)} class:sel={isSelected(c.addr, 1)} onclick={() => pick(c.addr)}>
          <span class="a">#{c.addr}</span>
          <span class="v">{cellText(c.words)}</span>
        </button>
      {/each}
    </div>
  {:else}
    <div class="grid">
      {#each cells as c}
        <button class="cell" class:written={cellWritten(c, 2)} class:sel={isSelected(c.addr, 2)} onclick={() => pick(c.addr)}>
          <span class="a">{c.addr}</span>
          <span class="v">{cellText(c.words)}</span>
        </button>
      {/each}
    </div>
  {/if}

  <p class="note">
    LM/GRF は 64-bit 長語（2語）単位、T はサイクル単位。オレンジ枠 = この行が書き込むセル。セルをクリックすると右の「値の来歴」がその値に切り替わります。
  </p>
</section>

<style>
  .mem {
    display: flex;
    flex-direction: column;
    min-height: 0;
    min-width: 0;
    width: 100%;
    gap: 4px;
    padding: 6px 8px;
    font-size: 12px;
    overflow: auto;
  }
  header {
    display: flex;
    align-items: center;
    gap: 4px;
    flex-wrap: wrap;
    min-width: 0;
  }
  .tabs {
    display: flex;
    gap: 3px;
  }
  .tabs button.on {
    background: var(--accent);
    color: var(--bg);
  }
  .where {
    color: var(--muted);
    margin-right: auto;
    font-family: var(--mono);
  }
  .pager {
    display: flex;
    align-items: center;
    gap: 4px;
    color: var(--muted);
    flex-wrap: wrap;
  }
  .pager span {
    font-family: var(--mono);
    min-width: 8em;
  }
  .pager input {
    width: 7em;
    padding: 1px 4px;
    font-family: var(--mono);
  }
  .grid {
    display: grid;
    grid-template-columns: repeat(auto-fill, minmax(90px, 1fr));
    gap: 2px;
    overflow-x: hidden;
    overflow-y: auto;
    align-content: start;
    min-height: 0;
    min-width: 0;
    width: 100%;
  }
  .grid.omr {
    grid-template-columns: repeat(auto-fill, minmax(86px, 1fr));
  }
  .tgrid {
    display: grid;
    gap: 4px;
  }
  .cell {
    display: flex;
    flex-direction: column;
    justify-content: center;
    text-align: left;
    font-family: var(--mono);
    font-size: 10px;
    padding: 2px 4px;
    min-width: 0;
    min-height: 33px;
    overflow: hidden;
  }
  .cell .a {
    display: block;
    color: var(--muted);
    font-size: 9px;
  }
  .cell .v {
    display: block;
    white-space: nowrap;
    overflow: hidden;
    text-overflow: ellipsis;
    font-size: 11px;
  }
  .cell.written {
    border-color: var(--c-compute);
    background: color-mix(in srgb, var(--c-compute) 14%, var(--panel));
  }
  .cell.sel {
    outline: 2px solid var(--accent);
    outline-offset: -2px;
  }
  .note {
    color: var(--muted);
    font-size: 11px;
    margin: 0;
  }
</style>
