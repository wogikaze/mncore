# MN-Core 2 データ移動ビジュアライザ

VSM プログラムが MN-Core 2 のメモリ階層の中でデータをどう動かすかを、SVG アニメーションで見るためのツール。
要件は `docs/dataflow-viz/REQUIREMENTS.md`、実測した仕様外の挙動は `docs/dataflow-viz/NUMERICS.md` にある。

| ディレクトリ | 内容 |
|---|---|
| `core/` | Rust のシミュレータ。公式エミュレータとビット単位で一致する（アセンブルできる全問題の解答で確認済み）。ハザード解析と可視化用の記録も行う |
| `wasm/` | `core` をブラウザから呼ぶための WebAssembly ラッパー |
| `web/` | サイト本体（Vite + Svelte 5 + GSAP） |

## サイトを動かす

```sh
cd viz/wasm && wasm-pack build --release --target web   # WebAssembly を作る
cd ../web
npm install
npm run sync-problems   # ../../problems をサイトにコピーする（git 管理外）
npm run dev             # http://localhost:5173
```

- 上部の **Now バー**：現在の行・命令・step・cycle・score と、選択中の Group / L1B / MAB / PE を常時表示する。
- 左の **VSM ソース**：現在行を強調し、NOP には「必要（理由）」か「削れる候補」を付ける。行をクリックすると全体がその行に追従する。
- 中央上の **チップ概要**：公式と同じ Group → 2 L2B → 8 L1B → 16 MAB → 4 PE のツリー。Group / L1B をクリックすると詳細を切り替える。「全体表示」でマップを拡大できる。
- 中央の **データフロー**：スコープ（全体 / Group / L1B / MAB / PE）を選び、読み出し元 → 演算器 → 書き込み先を大きく表示する。値は before / after、行の変更は下部の差分に出す。PE 表示では 4 サイクルと値の表示形式を切り替えられる。
- 「現在位置に追従」は既定で ON。命令が変わると、その命令が動かすスコープへ自動で切り替える。ユーザーがスコープやユニットを選ぶと OFF になり、選択は勝手に変わらない。
- 右の **詳細**：「値・競合」「メモリ」「占有」を切り替える。値をクリックすると来歴を表示し、入力クリックで根まで辿れる。
- 下部の **トランスポート**：再生、行/サイクル移動、速度、シーク、カテゴリ別の転送量。
- 左右・下・概要のペインはドラッグでリサイズでき、上部の「ソース / 概要 / 詳細 / 時間」で折りたたみできる。テーマはダークを既定にし、右上のアイコンでライトに切り替えられる。
- Story：スクロールに合わせて、ReLU、DRAM からの分配、行列積を順に解説する。

```sh
cd viz/web
npm run check   # svelte-check + tsc
npm test        # 来歴ウォークの回帰テスト
npm run build   # 静的サイトのビルド
```

## シミュレータのツール（`core/`）

公式のアセンブラとエミュレータ（`judge/`、`setup_judge.sh` で取得）を使う。

```sh
cd viz/core
cargo test --release
cargo run --release --bin difftest_prog -- ../../problems/39.matmul-trb-pkg-lmdram-256-1024-16  # 問題を公式エミュレータと比較
cargo run --release --bin difftest_fuzz -- 10 1 40   # ランダムな命令列で比較
cargo run --release --bin hazard_check -- ../../problems/*/main.vsm   # ハザード解析をアセンブラと照合
cargo run --release --bin viz_trace -- ../../problems/3.relu > trace.json   # 可視化用の記録
```

## ハザード解析の限界

PE メモリ、L1BM、L2BM の規則（SDM 3.6.3）は公式アセンブラの判定とほぼ一致する。
MV 命令が L2BM を読む規則（3.6.3.1）だけは、アセンブラが命令をパックしたときの発行時刻で判定しているため、再現できていない。
nop を減らすときは、公式ジャッジで確かめること。
