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

- Explorer：問題を選ぶか、VSM / testcase.vsm をドロップする。MAB を切り替えると、その MAB の4 PEを記録し直す。左のソースの nop には「必要（理由）」か「削れる候補」が付く。PE のセルをクリックすると値の来歴が出る。`PE メモリ` タブでは LM0/LM1/GRF/T/OMR の任意の番地をクリックでき、来歴の入力を辿ると依存の根まで移動できる。←→ でステップ移動、Space で再生。
- 上部の階層ビュー：公式と同じ Group → 2 L2B → 8 L1B → 16 MAB → 4 PE のツリー。L1B タイルをクリックすると、その L1B の 16 MAB、共有 L1BM、フォーカス MAB の4 PEの値が開く。色付きの枠と線が現在行の転送経路を示す。
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
