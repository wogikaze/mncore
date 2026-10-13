<script lang="ts">
  import { app } from '../lib/state.svelte';
  import { GROUPS, MAU_GROUPS, occupancy } from '../lib/occupancy';

  const CW = 8;
  const RH = 16;

  const occ = $derived(app.trace ? occupancy(app.trace) : null);
  // Rows: always the main groups; optional ones only when used.
  const rows = $derived(
    GROUPS.filter((g) => ['alu', 'mau-calc', 'mau-mwrite', 'mau-mread', 'l1bm', 'l2bm', 'mv', 'nop'].includes(g.id) || (occ?.counts[g.id] ?? 0) > 0),
  );
  const current = $derived(app.trace?.lines[app.line]);

  let scroller: HTMLDivElement | undefined = $state();
  $effect(() => {
    const s = current?.step ?? 0;
    if (!scroller) return;
    const x = s * CW;
    if (x < scroller.scrollLeft + 40 || x > scroller.scrollLeft + scroller.clientWidth - 40) {
      scroller.scrollLeft = x - scroller.clientWidth / 2;
    }
  });

  function cellClass(gid: string, step: number): string {
    const c = occ!.cells[step];
    if (!c.has(gid)) return '';
    if (MAU_GROUPS.includes(gid) && MAU_GROUPS.filter((g) => c.has(g)).length >= 2) return 'full';
    return gid === 'nop' ? 'nopc' : gid === 'mv' ? 'mvc' : 'used';
  }

  function seekStep(step: number) {
    const l = occ?.lineOf[step];
    if (l !== undefined && l >= 0) app.seek(l);
  }

  const pct = (n: number) => (occ && occ.steps ? Math.round((n / occ.steps) * 100) : 0);
</script>

<section class="occ">
  {#if occ}
    <div class="summary">
      <div>
        <b>スコア {occ.steps}</b>
        <span class="muted">（PE {occ.steps - (occ.counts['mv'] ?? 0)} ＋ MV {occ.counts['mv'] ?? 0}）</span>
      </div>
      <div title="依存関係とハザードを無視し、命令グループの使用回数だけから求めた下限。">
        資源から見た下限 <b>{occ.bound.total}</b>
        <span class="muted">（PE {occ.bound.peSteps}：{GROUPS.find((g) => g.id === occ.bound.limitedBy)?.label ?? occ.bound.limitedBy} ＋ MV {occ.bound.mvLines}）</span>
      </div>
      <div>
        nop <b>{occ.counts['nop'] ?? 0}</b> ステップ・1グループだけのステップ <b>{occ.single}</b>・MAU 2グループ同時 <b>{occ.mauFull}</b>
      </div>
    </div>
    <div class="grid">
      <div class="labels">
        {#each rows as g}
          <div class="label" style:height="{RH}px">
            <span>{g.label}</span>
            <span class="count">{occ.counts[g.id] ?? 0}<small>（{pct(occ.counts[g.id] ?? 0)}%）</small></span>
          </div>
        {/each}
      </div>
      <div class="scroll" bind:this={scroller}>
        <svg width={occ.steps * CW} height={rows.length * RH}>
          {#each rows as g, r}
            <rect class="rowbg" x="0" y={r * RH} width={occ.steps * CW} height={RH - 1} />
          {/each}
          {#each occ.cells as _, s}
            {#each rows as g, r}
              {@const cls = cellClass(g.id, s)}
              {#if cls}
                <rect class={cls} x={s * CW} y={r * RH + 1} width={CW - 1} height={RH - 3}>
                  <title>step {s}: {app.trace?.lines[occ.cells[s].get(g.id) ?? 0]?.text}</title>
                </rect>
              {/if}
            {/each}
          {/each}
          {#if current}
            <rect class="cursor" x={current.step * CW - 1} y="0" width={Math.max(1, current.words) * CW + 1} height={rows.length * RH} />
          {/if}
          <!-- Clickable columns. -->
          {#each occ.cells as _, s}
            <rect class="hit" x={s * CW} y="0" width={CW} height={rows.length * RH} role="button" tabindex="-1" onclick={() => seekStep(s)} onkeydown={() => {}} />
          {/each}
        </svg>
      </div>
    </div>
    <p class="note">
      1ステップに各グループ1つまで、MAU の3グループは2つまで（同じ精度のとき）同時に発行できる（SDM 3.6.4）。
      空いている枠は、依存関係とハザードが許せば、ほかの命令を詰められる場所。
    </p>
  {/if}
</section>

<style>
  .occ {
    min-width: 0;
    display: flex;
    flex-direction: column;
    min-height: 0;
    font-size: 12px;
    padding: 6px 8px;
    gap: 6px;
  }
  .summary {
    display: flex;
    flex-wrap: wrap;
    gap: 6px 24px;
  }
  .muted,
  .note {
    color: var(--muted);
  }
  .note {
    font-size: 11px;
    margin: 0;
  }
  .grid {
    display: flex;
    min-height: 0;
    min-width: 0;
  }
  .labels {
    flex: none;
    width: 150px;
  }
  .label {
    display: flex;
    justify-content: space-between;
    align-items: center;
    padding-right: 8px;
    font-size: 11px;
  }
  .count {
    font-family: var(--mono);
    color: var(--muted);
  }
  .count small {
    font-size: 9px;
  }
  .scroll {
    overflow-x: auto;
    flex: 1;
  }
  .rowbg {
    fill: var(--panel);
  }
  .used {
    fill: var(--c-l2);
  }
  .full {
    fill: var(--c-mau);
  }
  .mvc {
    fill: var(--c-offchip);
  }
  .nopc {
    fill: var(--warn);
    opacity: 0.6;
  }
  .cursor {
    fill: none;
    stroke: var(--fg);
    stroke-width: 1.5;
  }
  .hit {
    fill: transparent;
    cursor: pointer;
  }
</style>
