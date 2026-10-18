<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { chainFrom, forwarded, producer, type Origin } from '../lib/provenance';
  import { format } from '../lib/numbers';
  import { read } from '../lib/memory';
  import { locLabel, peSummary, type ValueRow } from '../lib/hierarchy';
  import type { Access } from '../lib/types';

  const trace = $derived(app.trace);
  const line = $derived(trace?.lines[app.line]);
  const sel = $derived(app.selection);
  const selLine = $derived(sel?.line ?? app.line);

  const unitNames: Record<string, string> = {
    alu: 'ALU',
    mau: 'MAU（ベクトル）',
    matrix: 'MAU（行列ベクトル積）',
    mwrite: '行列レジスタ書き込み',
    mread: '行列レジスタ転置読み出し',
    'l1-to-pe': 'L1BM → PE',
    'pe-to-l1': 'PE → L1BM',
    l2: 'L2BM ↔ L1BM',
    wait: 'MV 待ち合わせ',
    noforward: 'フォワーディング更新なし',
    other: 'その他',
  };

  const related = $derived.by(() => {
    const hs = trace?.hazards.filter((h) => h.from === app.line || h.to === app.line) ?? [];
    const groups = new Map<string, { h: (typeof hs)[number]; units: number[] }>();
    for (const h of hs) {
      const m = h.res.match(/^(\w+)\((\d+)\)$/);
      const base = m ? m[1] : h.res;
      const key = [h.rule, h.kind, base, h.addr, h.from, h.to, h.distance, h.required].join('|');
      const g = groups.get(key);
      if (g) {
        if (m) g.units.push(+m[2]);
      } else groups.set(key, { h: { ...h, res: base }, units: m ? [+m[2]] : [] });
    }
    return [...groups.values()].map(({ h, units }) => ({
      ...h,
      res: units.length ? `${h.res}（${units.length > 1 ? `${Math.min(...units)}〜${Math.max(...units)}` : units[0]}）` : h.res,
    }));
  });

  const origins = $derived.by<Origin[]>(() => {
    if (!trace || !sel) return [];
    return chainFrom(trace, sel);
  });

  const summary = $derived(peSummary(line, app.pe, app.view));

  function describe(a: Access): string {
    const v = format(a.words.slice(0, app.view === 'f64' ? 2 : a.loc === 't' ? 2 : a.words.length), app.view).join(', ');
    const where =
      a.loc === 'out'
        ? `結果 c${a.cycle}`
        : a.addr === null
          ? `$${a.loc}`
          : a.loc === 't'
            ? `T c${a.addr}`
            : `${a.loc}[${a.addr}]`;
    return `${where} = ${v}`;
  }

  function origin(a: Access, at: number): Origin | null {
    if (!trace) return null;
    if (a.addr === null) return forwarded(trace, a.unit, a.loc, a.cycle, at);
    return producer(trace, a.unit, a.loc, a.addr, at - 1);
  }

  /** Old value of a write in the current line, for before → after. */
  function oldWords(r: ValueRow): number[] | null {
    if (!app.timeline || r.addr === null) return null;
    const per = r.loc === 't' ? 4 : 1;
    const base = r.addr * per;
    const unit = r.loc === 'l1bm' ? `l1b:${app.focusL1b}` : `pe:${app.pe}`;
    return Array.from({ length: r.words.length }, (_, i) => read(app.before, unit, r.loc, base + i) ?? 0);
  }

  function changed(r: ValueRow): boolean {
    const old = oldWords(r);
    return Boolean(old && old.some((v, i) => v !== r.words[i]));
  }

  function preview(words: number[], n = 2): string {
    const vals = format(words, app.view);
    return vals.length > n ? `${vals.slice(0, n).join(' ')}…` : vals.join(' ');
  }

  function rowText(r: ValueRow): string {
    return `${locLabel(r.loc, r.addr)} = ${preview(r.words, 4)}`;
  }

  function openRow(r: ValueRow, write: boolean) {
    const loc = r.loc === 'l1bm_src' ? 'l1bm' : r.loc;
    const unit = r.loc === 'l1bm_src' ? Math.floor(app.pe / 64) : app.pe;
    app.selection = { unit, loc, addr: r.addr, line: write ? app.line : app.line - 1 };
    app.detailTab = 'values';
  }
</script>

<aside class="inspector">
  {#if trace}
    <section class="card summary">
      <div class="kv">
        <span>SCORE</span><b>{trace.score}</b>
        <span>出力</span>
        {#if trace.output.values}
          <b class:good={trace.output.failures === 0} class:bad={trace.output.failures > 0}>
            {trace.output.failures === 0 ? '正解' : `${trace.output.failures} 値が誤差超過`}（{trace.output.values} 値）
          </b>
          <span>最大誤差</span>
          <b>{trace.output.max_abs_error.toExponential(2)} / 許容 {trace.output.atol || '完全一致'}</b>
        {:else}
          <b>—</b>
        {/if}
      </div>
      {#if trace.output.first_failure}<p class="bad">{trace.output.first_failure}</p>{/if}
      {#if trace.error}<p class="bad">停止: {trace.error}</p>{/if}
    </section>

    {#if sel}
      <section class="card">
        <h3>
          選択中の値
          <button class="clear" onclick={() => (app.selection = null)}>解除</button>
        </h3>
        <p class="where">
          {sel.loc === 'l1bm' ? `L1B #${sel.unit}` : `PE #${sel.unit}`} の
          {sel.addr !== null ? locLabel(sel.loc, sel.addr) : `$${sel.loc}`}
          {#if sel.addr === null}
            （{trace.lines[selLine]?.lineno}行目で読んだ値）
          {:else if selLine < 0}
            （初期状態）
          {:else}
            （{trace.lines[selLine]?.lineno}行目の時点）
          {/if}
        </p>
        <p class="hint">入力の値をクリックすると、その来歴に切り替わります。</p>
        <ol class="chain">
          {#each origins as o}
            <li>
              <button class="stepbtn" onclick={() => o.line >= 0 && app.seek(o.line)}>
                {o.line >= 0 ? `${trace.lines[o.line].lineno}行` : '初期値'}
              </button>
              <code>{o.expr}</code>
              <div class="muted">サイクル {o.write.cycle}: {describe(o.write)}</div>
              {#if o.inputs.length}
                <div class="inputs">
                  入力:
                  {#each o.inputs as inp}
                    {@const up = origin(inp, o.line)}
                    <button
                      class="input"
                      title={up ? `${up.line >= 0 ? trace.lines[up.line].lineno + '行' : '初期値'}: ${up.expr}` : 'この値の書き込みは記録にありません'}
                      onclick={() => app.followInput(inp, o.line)}
                    >{describe(inp)}</button>
                  {/each}
                </div>
              {/if}
            </li>
          {:else}
            <li class="muted">この位置への書き込みは記録にありません（初期値 0）。</li>
          {/each}
        </ol>
      </section>
    {:else if line}
      <section class="card">
        <h3>
          {line.lineno}行目
          <span class="step">step {line.step}{line.words > 1 ? `〜${line.step + line.words - 1}` : ''}</span>
        </h3>
        <code class="instr">{line.text}</code>
        {#each line.exprs as e}
          <div class="expr"><span class="unit">{unitNames[e.unit] ?? e.unit}</span> {e.text}{e.fwd ? ` → $${e.fwd}` : ''}</div>
        {/each}
      </section>

      <section class="card">
        <h3>この行の値 <span class="step">PE {app.pe}</span></h3>
        {#if line.kind !== 'pe'}
          <p class="hint">MV / nop は PE のローカル値を更新しません。転送は「全体」「Group」「L1B」表示で確認できます。</p>
        {:else}
          <div class="vsec">
            <h4>読み出し</h4>
            {#each summary.reads.slice(0, 5) as r}
              <button class="vrow" onclick={() => openRow(r, false)}><code>{rowText(r)}</code></button>
            {:else}
              <div class="muted">なし</div>
            {/each}
          </div>
          <div class="vsec">
            <h4>書き込み</h4>
            {#each summary.writes.slice(0, 5) as r}
              {@const old = oldWords(r)}
              <button class="vrow" class:changed={changed(r)} onclick={() => openRow(r, true)}>
                <span class="loc">{locLabel(r.loc, r.addr)}</span>
                {#if old && changed(r)}
                  <span class="old">{preview(old, 2)}</span>
                  <span class="arrow">→</span>
                {/if}
                <code title={format(r.words, app.view).join(' ')}>{preview(r.words, 2)}</code>
              </button>
            {:else}
              <div class="muted">なし</div>
            {/each}
          </div>
          <p class="hint">値の行をクリックすると、その来歴を表示します。</p>
        {/if}
      </section>
    {/if}

    {#if related.length}
      <section class="card">
        <h3>この行の競合</h3>
        <ul class="hazards">
          {#each related as h}
            <li class:bad={h.distance < h.required}>
              <b>{h.rule}</b> {h.kind === 'data race' ? 'データ競合' : 'ポート衝突'}
              {h.res}{h.addr !== null ? `@${h.addr}` : ''}:
              {trace.lines[h.from].lineno}行 → {trace.lines[h.to].lineno}行、
              {h.distance}/{h.required} サイクル
            </li>
          {/each}
        </ul>
      </section>
    {/if}
  {:else if app.loading}
    <p class="muted">シミュレーション中…</p>
  {/if}
</aside>

<style>
  .inspector {
    overflow: auto;
    font-size: 12px;
    padding: 6px 8px 12px;
    display: flex;
    flex-direction: column;
    gap: 6px;
    width: 100%;
  }
  .card {
    background: var(--panel-2);
    border: 1px solid var(--line);
    border-radius: 5px;
    padding: 6px 8px;
  }
  .summary .kv {
    display: grid;
    grid-template-columns: auto 1fr;
    gap: 1px 10px;
  }
  .summary .kv span {
    color: var(--muted);
    font-size: 10px;
  }
  .summary .kv b {
    font-family: var(--mono);
    font-size: 11px;
  }
  h3 {
    display: flex;
    align-items: baseline;
    justify-content: space-between;
    gap: 6px;
    margin: 0 0 4px;
    font-size: 12px;
    color: var(--fg);
  }
  h4 {
    margin: 0 0 2px;
    font-size: 10px;
    color: var(--muted);
    font-weight: 600;
  }
  .step {
    font-family: var(--mono);
    font-size: 10px;
    color: var(--muted);
    font-weight: 400;
  }
  code {
    font-family: var(--mono);
    font-size: 11px;
    white-space: pre-wrap;
    word-break: break-all;
  }
  .instr {
    display: block;
    font-size: 12px;
    color: var(--fg);
    margin-bottom: 3px;
  }
  .expr {
    font-family: var(--mono);
    font-size: 10px;
    color: var(--muted);
    margin-top: 2px;
  }
  .unit {
    font-family: var(--sans);
    font-size: 9px;
    background: var(--panel);
    border: 1px solid var(--line);
    padding: 0 3px;
    border-radius: 2px;
    color: var(--fg);
  }
  .where {
    margin: 0 0 2px;
    font-family: var(--mono);
    color: var(--fg);
  }
  .hint {
    color: var(--muted);
    font-size: 10px;
    margin: 3px 0 0;
  }
  .vsec {
    display: flex;
    flex-direction: column;
    gap: 1px;
    margin-bottom: 4px;
  }
  .vrow {
    all: unset;
    display: flex;
    align-items: baseline;
    gap: 4px;
    font-family: var(--mono);
    font-size: 10px;
    white-space: nowrap;
    overflow: hidden;
    text-overflow: ellipsis;
    cursor: pointer;
    max-width: 100%;
    border-radius: 2px;
    padding: 0 2px;
  }
  .loc {
    color: var(--muted);
    flex: none;
    min-width: 48px;
  }
  .vrow:hover {
    background: var(--hover);
  }
  .vrow.changed code {
    color: var(--c-compute);
    font-weight: 600;
  }
  .old {
    color: var(--muted);
  }
  .arrow {
    color: var(--muted);
  }
  .chain {
    padding-left: 16px;
    margin: 4px 0 0;
  }
  .chain li {
    margin-bottom: 6px;
  }
  .stepbtn {
    font-size: 10px;
    padding: 0 4px;
  }
  .inputs {
    font-family: var(--mono);
    font-size: 9px;
    display: flex;
    flex-wrap: wrap;
    gap: 3px;
    margin-top: 2px;
  }
  .input {
    font-family: var(--mono);
    font-size: 9px;
    padding: 0 3px;
    background: var(--panel);
  }
  .input:hover {
    border-color: var(--accent);
    color: var(--accent);
  }
  .hazards {
    margin: 0;
    padding-left: 14px;
    font-size: 10px;
    line-height: 1.4;
  }
  .hazards li {
    margin-bottom: 2px;
  }
  .clear {
    font-size: 9px;
    padding: 0 4px;
  }
  .muted {
    color: var(--muted);
  }
  .good {
    color: var(--good);
  }
  .bad {
    color: var(--bad);
  }
</style>
