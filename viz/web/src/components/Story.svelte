<script lang="ts">
  import { onMount } from 'svelte';
  import gsap from 'gsap';
  import { ScrollTrigger } from 'gsap/ScrollTrigger';
  import { app } from '../lib/state.svelte';
  import ChipView from './ChipView.svelte';
  import PeView from './PeView.svelte';

  gsap.registerPlugin(ScrollTrigger);

  interface Section {
    problem: string;
    /** Range of line indices (0-based, inclusive) played while scrolling the section. */
    from: number;
    to: number;
    title: string;
    body: string[];
    /** Show the reasons of the nops in this range from the trace. */
    nops?: boolean;
  }

  const sections: Section[] = [
    {
      problem: '3.relu',
      from: 0,
      to: 1,
      title: '1命令は、4096個の PE で4サイクル動く',
      body: [
        'ReLU の解答は2行しかない。1行目の frelu $lm0v $lm0v $ln0v は、LM0 から長語を読み、ALU で ReLU を計算して LM1 に書く。',
        'この1行が、チップ上の4096個すべての PE で同時に、4サイクル続けて実行される。$lm0v の v は、サイクルごとにアドレスを1長語ずつ進める指定だ。下の図では、注目している MAB の4つの PE で、サイクルごとに値が LM0 から ALU を通って LM1 に入る。',
        'スコアは発行した命令語の数で数える。この解答は2ステップ、つまりスコア2になる。',
      ],
    },
    {
      problem: '17.dram-dl-256-16',
      from: 0,
      to: 4,
      title: 'DRAM から PE まで、階段を4段降りる',
      body: [
        'PE は DRAM を直接読めない。DRAM → L2BM → L1BM → PE と、メモリの階層を1段ずつ降りる必要がある。',
        '最初の2行は MV 命令で、4つのグループの DRAM から、それぞれのグループの L2BM に 256 長語ずつ運ぶ。@.0 と @.1 で、グループ内の2つの L2B に分けている。',
        '3行目の l2bmd は L2BM から配下の8個の L1BM に分配し、5行目の l1bmm で L1BM から PE に配る。上の図で、粒子が階層を下っていく。',
        'その間の nop は、L2BM → L1BM の書き込みが終わる前に、同じアドレスを L1BM → PE 転送で読まないためにある。',
      ],
      nops: true,
    },
    {
      problem: '39.matmul-trb-pkg-lmdram-256-1024-16',
      from: 0,
      to: 5,
      title: '行列積は、ブロックフロート化から始まる',
      body: [
        '256×1024 の A と 16×1024 の B から C = A × Bᵀ を作る。各 MAB は、A と B の一部を LM0 に持っている。',
        'MAU の行列演算は、入力がブロックフロート（ブロック内で指数を揃えた形式）であることを要求する。gbfn で疑似単精度のブロックフロートに変換し、その結果を $aluf フォワーディングで次のステップの gmwrite に渡して、行列レジスタ $ly に書く。',
        '6行目の gmmul で、行列レジスタと、同じくブロックフロート化した A の行との行列ベクトル積を計算し、LM1 に書く。',
      ],
    },
    {
      problem: '39.matmul-trb-pkg-lmdram-256-1024-16',
      from: 6,
      to: 95,
      title: '同じ型を16回繰り返す',
      body: [
        'B の行の組を入れ替えながら、gbfn → gmwrite → gmmul の6ステップを16回繰り返す。結果は LM1 の別々の場所に貯まっていく。',
        'この段階のデータは、ほとんど PE の中だけで動いている。上の図では、チップ規模の転送はなく、PE の帯が演算で光るだけだ。',
      ],
    },
    {
      problem: '39.matmul-trb-pkg-lmdram-256-1024-16',
      from: 96,
      to: 113,
      title: 'MAB 方向に足し合わせる',
      body: [
        '各 MAB の結果は、1024 の内積のうちの一部分でしかない。l1bmrffadd で、L1B 配下の16個の MAB の値を足し合わせ、L1BM に書く。この縮約は4つずつ2段で行われ、1段目の結果は単精度に丸められる。',
        'その前の2つの nop は、直前の gmmul が LM1 に書いた値を、L1BM への転送で読むための間隔だ。',
      ],
      nops: true,
    },
    {
      problem: '39.matmul-trb-pkg-lmdram-256-1024-16',
      from: 114,
      to: 122,
      title: 'L2BM で集めて、DRAM へ',
      body: [
        'l2bmrffadd で、L2B 配下の8個の L1BM を足し合わせて L2BM に上げる。最後の MV 命令で、L2BM から各グループの DRAM に書き出す。',
        'ここで計算した C は、テストケースの期待値と許容誤差の範囲で一致する。右上の結果欄で、最大誤差と許容誤差を確かめられる。',
      ],
      nops: true,
    },
  ];

  let els: HTMLElement[] = $state([]);
  let scroller: HTMLElement | undefined = $state();
  let active = $state(0);
  let loadingFor: string | null = null;

  async function enter(i: number) {
    active = i;
    const s = sections[i];
    if (app.problem !== s.problem && loadingFor !== s.problem) {
      loadingFor = s.problem;
      app.line = s.from;
      await app.open(s.problem);
      loadingFor = null;
      // The reader may have moved on while loading.
      const now = sections[active];
      if (now.problem !== app.problem) enter(active);
      else app.seek(Math.max(now.from, Math.min(now.to, app.line)));
    }
  }

  onMount(() => {
    app.playing = false;
    const triggers = sections.map((s, i) =>
      ScrollTrigger.create({
        trigger: els[i],
        scroller,
        start: 'top 60%',
        end: 'bottom 60%',
        onEnter: () => enter(i),
        onEnterBack: () => enter(i),
        onUpdate: (self) => {
          if (active !== i || !app.trace || app.problem !== s.problem) return;
          const line = s.from + Math.round(self.progress * (s.to - s.from));
          if (line !== app.line) app.seek(line);
        },
      }),
    );
    enter(0);
    return () => triggers.forEach((t) => t.kill());
  });

  const nopReasons = $derived.by(() => {
    const s = sections[active];
    const t = app.trace;
    if (!s.nops || !t || app.problem !== s.problem) return [];
    return t.nops
      .filter((n) => n.line >= s.from && n.line <= s.to)
      .map((n) => ({
        line: t.lines[n.line].lineno,
        reasons: n.needed_by.map((k) => t.hazards[k]),
      }));
  });
</script>

<div class="story" bind:this={scroller}>
  <article>
    {#each sections as s, i}
      <section bind:this={els[i]} class:active={active === i}>
        <p class="tag">{s.problem}</p>
        <h2>{s.title}</h2>
        {#each s.body as p}
          <p>{p}</p>
        {/each}
        {#if active === i && nopReasons.length}
          <div class="nops">
            {#each nopReasons as n}
              <p>
                <b>{n.line}行目の nop</b>：
                {#if n.reasons.length}
                  {#each n.reasons as h}
                    {h.rule} {h.kind === 'data race' ? 'データ競合' : 'ポート衝突'}（{h.res}{h.addr !== null ? `@${h.addr}` : ''}、{app.trace?.lines[h.from].lineno}行の書き込み → {app.trace?.lines[h.to].lineno}行の読み出し、必要 {h.required} サイクルに対して {h.distance}）。
                  {/each}
                {:else}
                  どの規則にも必要とされていない。1ステップ削れる候補。
                {/if}
              </p>
            {/each}
          </div>
        {/if}
      </section>
    {/each}
    <div class="end">Explorer モードで、ほかの問題や自分の解答を同じように見られます。</div>
  </article>
  <aside class="stage">
    {#if app.trace}
      {@const l = app.trace.lines[app.line]}
      <div class="now"><span>{l?.lineno}行目 ・ step {l?.step}</span><code>{l?.text}</code></div>
    {/if}
    <div class="chip"><ChipView /></div>
    <div class="pe"><PeView /></div>
  </aside>
</div>

<style>
  .story {
    flex: 1;
    min-height: 0;
    overflow-y: auto;
    display: grid;
    grid-template-columns: minmax(300px, 34%) 1fr;
  }
  article {
    padding: 0 28px 40vh;
  }
  section {
    min-height: 120vh;
    padding-top: 30vh;
    opacity: 0.45;
    transition: opacity 0.3s;
  }
  section.active {
    opacity: 1;
  }
  .tag {
    font-family: var(--mono);
    font-size: 11px;
    color: var(--muted);
    margin: 0;
  }
  h2 {
    font-size: 20px;
    margin: 4px 0 12px;
  }
  p {
    line-height: 1.8;
    font-size: 14px;
  }
  .nops {
    border-left: 3px solid var(--warn);
    padding-left: 10px;
    font-size: 13px;
  }
  .nops p {
    font-size: 13px;
    margin: 4px 0;
  }
  .end {
    color: var(--muted);
    padding: 20vh 0;
  }
  .stage {
    position: sticky;
    top: 0;
    height: calc(100vh - 42px);
    display: grid;
    grid-template-rows: auto minmax(0, 0.8fr) minmax(0, 1.2fr);
    border-left: 1px solid var(--line);
  }
  .now {
    display: flex;
    gap: 12px;
    padding: 6px 10px;
    font-size: 12px;
    border-bottom: 1px solid var(--line);
    color: var(--muted);
  }
  .now code {
    font-family: var(--mono);
    color: var(--fg);
  }
  .chip,
  .pe {
    display: flex;
    min-height: 0;
  }
  .chip > :global(*),
  .pe > :global(*) {
    flex: 1;
  }
</style>
