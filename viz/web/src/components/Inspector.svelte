<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { chain, forwarded, producer, type Origin } from '../lib/provenance';
  import { format } from '../lib/numbers';
  import type { Access } from '../lib/types';

  const trace = $derived(app.trace);
  const line = $derived(trace?.lines[app.line]);
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

  // Hazards that differ only in the L1B or L2B number are shown once, with the range of units.
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
    const s = app.selection;
    if (!trace || !s) return [];
    return chain(trace, s.unit, s.loc, s.addr, app.line);
  });

  function describe(a: Access): string {
    const v = format(a.words.slice(0, app.view === 'f64' ? 2 : a.loc === 't' ? 2 : a.words.length), app.view).join(', ');
    const where = a.addr === null ? `$${a.loc}` : a.loc === 't' ? `T c${a.addr}` : `${a.loc}[${a.addr}]`;
    return `${where} = ${v}`;
  }

  // Expand one input of an origin one level further.
  function origin(a: Access, at: number): Origin | null {
    if (!trace) return null;
    if (a.addr === null) return forwarded(trace, a.unit, a.loc, a.cycle, at);
    return producer(trace, a.unit, a.loc, a.addr, at - 1);
  }
</script>

<aside class="inspector">
  {#if trace}
    <section>
      <h3>結果</h3>
      <div class="kv">
        <span>スコア</span><b>{trace.score}</b>
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

    {#if line}
      <section>
        <h3>{line.lineno}行目（step {line.step}{line.words > 1 ? `〜${line.step + line.words - 1}` : ''}）</h3>
        <code>{line.text}</code>
        {#each line.exprs as e, i}
          <div class="expr"><span class="unit">{unitNames[e.unit]}</span> {e.text}{e.fwd ? `（→ $${e.fwd}）` : ''}</div>
        {/each}
        {#if related.length}
          <h4>この行が関わる競合</h4>
          <ul>
            {#each related as h}
              <li class:bad={h.distance < h.required}>
                {h.rule} {h.kind === 'data race' ? 'データ競合' : 'ポート衝突'} {h.res}{h.addr !== null ? `@${h.addr}` : ''}:
                {trace.lines[h.from].lineno}行 → {trace.lines[h.to].lineno}行、間隔 {h.distance} / 必要 {h.required} サイクル
              </li>
            {/each}
          </ul>
        {/if}
      </section>
    {/if}

    <section>
      <h3>値の来歴</h3>
      {#if !app.selection}
        <p class="muted">PE のセルをクリックすると、その値がどこから来たかをさかのぼります。</p>
      {:else}
        <p class="muted">PE #{app.selection.unit} の {app.selection.loc}[{app.selection.addr}]（{line?.lineno}行目の時点）</p>
        <ol class="chain">
          {#each origins as o}
            <li>
              <button onclick={() => o.line >= 0 && app.seek(o.line)}>
                {o.line >= 0 ? `${trace.lines[o.line].lineno}行` : '初期値'}
              </button>
              <code>{o.expr}</code>
              <div class="muted">サイクル {o.write.cycle}: {describe(o.write)}</div>
              {#if o.inputs.length}
                <div class="inputs">
                  入力:
                  {#each o.inputs as inp}
                    {@const up = origin(inp, o.line)}
                    <span title={up ? `${up.line >= 0 ? trace.lines[up.line].lineno + '行' : '初期値'}: ${up.expr}` : ''}>{describe(inp)}</span>
                  {/each}
                </div>
              {/if}
            </li>
          {:else}
            <li class="muted">この位置への書き込みは記録にありません（初期値 0）。</li>
          {/each}
        </ol>
      {/if}
    </section>
  {:else if app.loading}
    <p class="muted">シミュレーション中…</p>
  {/if}
</aside>

<style>
  .inspector {
    overflow: auto;
    font-size: 12px;
    padding: 0 10px 10px;
  }
  h3 {
    font-size: 12px;
    margin: 12px 0 4px;
    color: var(--muted);
    font-weight: 600;
  }
  h4 {
    font-size: 11px;
    margin: 8px 0 2px;
    color: var(--muted);
  }
  .kv {
    display: grid;
    grid-template-columns: auto 1fr;
    gap: 2px 10px;
  }
  code {
    display: block;
    font-family: var(--mono);
    font-size: 11px;
    white-space: pre-wrap;
    word-break: break-all;
  }
  .expr {
    font-family: var(--mono);
    font-size: 11px;
    margin-top: 2px;
  }
  .unit {
    font-family: var(--sans);
    font-size: 10px;
    background: var(--panel);
    border: 1px solid var(--line);
    padding: 0 4px;
    border-radius: 3px;
  }
  ul {
    margin: 0;
    padding-left: 16px;
  }
  .chain {
    padding-left: 18px;
    margin: 4px 0;
  }
  .chain li {
    margin-bottom: 8px;
  }
  .chain button {
    font-size: 11px;
  }
  .inputs {
    font-family: var(--mono);
    font-size: 10px;
    display: flex;
    flex-wrap: wrap;
    gap: 4px;
  }
  .inputs span {
    background: var(--panel);
    padding: 0 3px;
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
