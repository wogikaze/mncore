# mncompile — 汎用 MN-Core 2 コンパイラ

普通の Python で書いたカーネルと、入出力テンソルの「契約」（型・値域・物理配置・許容誤差）だけから
MN-Core 2 の VSM を生成するコンパイラ。問題ごとの専用カーネルや手書きアセンブリは持たない。

- コンパイラが受け取るのは `kernel(...)` のソースと契約だけ。問題名・テストケース・参照解は読まない
  （それらを読むのはベンチマークのハーネス `mncompile/bench/` だけ）。
- 命令は構造化した表現（`machine.py`）で扱い、ISA の全オペコード・全オペランド形式を表現・出力できる
  （ALU・MAU・行列レジスタ読み書き・L1BM・L2BM・MV・wait・noforward・nop。リポジトリ中の全 VSM で往復テスト済み）。
- 戦略ごとに候補プログラムを作り、スケジュールし、シミュレータで検証して、検証を通った中で最短の行数のものを選ぶ。
- 許容誤差がある場合は近似の強さ（Newton 反復回数、exp の多項式次数、誤差予算内に収まる項の削除）を探索し、
  誤差予算の 8 割以内に収まる最短の候補を選ぶ。

ベンチマーク結果は末尾の表を参照。

## 使い方

```sh
cargo build --release --manifest-path mncompile/native/Cargo.toml   # 検証用シミュレータ（初回のみ）
python3 -m mncompile mncompile/examples/sigmoid_like.py \
  --contract mncompile/examples/sigmoid_like.json --output /tmp/out
```

`kernel.vsm` と `report.json`（選ばれた戦略、全候補の行数、不採用理由）が出力される。
公式アセンブラ・エミュレータ（リポジトリ直下の `judge/`、`https://mncore-challenge.preferred.jp/judge.zip`）が必要。

契約は問題文の宣言と同じ書式。

```json
{"inputs":  [{"name": "A", "dtype": "Float", "memory": "$lm[0:16]",
              "layout": "(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1); B@[MAB])",
              "low": -8, "high": 8}],
 "outputs": [{"name": "C", "dtype": "Float", "memory": "$ln[0:16]",
              "layout": "(256,16)/((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))", "atol": 1e-6}]}
```

### 誤差予算で変わるコード

```python
def kernel(a):
    return [[v + 0.001 * v * v for v in row] for row in a]
```

入力範囲 `[-1, 1]` で、`atol=1e-5` なら 5 行（`fvmul` + `fvfma`）、`atol=0.002` なら区間解析で
`0.001*v*v` の大きさ（≤0.001）が予算に収まるので項を落とし、1 行（2 長語コピー `lpassa $llm0v $lln0v`）になる。

## 構成

| モジュール | 役割 |
| --- | --- |
| `layout.py` | 公式の配置記法（`(4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1); B@[MAB]` など）の解析と物理位置計算 |
| `trace.py`, `ir.py` | カーネルの記号実行。ハッシュコンシングした式グラフ（n 項 sum/max/lor、比較、select、gather 等） |
| `oracle.py`, `verify.py` | 参照実行（binary64 → 出力型に丸め）と検証。網羅入力と独立ランダム入力を交互に使う |
| `sim.py`, `native/` | 検証用ネイティブシミュレータ（Rust）と公式アセンブラ・エミュレータの呼び出し。ネイティブ側が正確に模擬しない命令（hv*/hm*/ilrelud/DAR）を含む場合は自動で公式エミュレータを使う |
| `machine.py` | 構造化命令。全オペコード・オペランド形式の出力、並列発行グループ、読み書きするメモリ語の計算 |
| `vprog.py`, `schedule.py` | SSA 風の仮想命令列と VLIW リストスケジューラ（フォワーディング、GRF/T への格納割当て、読み出しポート制約、マスク entry 管理、レジスタ圧迫の考慮、デッドロック時の再計算・ポートコピー）。アセンブラが拒否した行は分割して修復し、不要な nop はアセンブラが受理する限り削る |
| `select.py` | スカラ関数の命令選択（整数/浮動小数表現、定数、select、除算、exp、PE 座標定数、PE 間交換、ビット置換） |
| `compiler.py` | 戦略の実行、候補の検証、最短の選択 |

### 戦略

| 戦略 | 対象 |
| --- | --- |
| `local` | 各出力語が同じ PE の入力の同じ関数（SPMD）。PE 座標に依存する定数は `$peid`/`$mabid` 等のビット線形結合で生成、MAB 内の別 PE の入力は `msl`/`msr` 回転と PE マスクで取得、PE ごとにアドレスがずれる入力は T 間接参照（複数テンソルなら T を切り替えて GRF に退避）。出力が入力と同じ LM にある場合は GRF に計算して 2 長語コピーする変種も作る |
| `relayout` | レーンがずれた入力（行ベクトルの放送など）。ずれた部分式を元の位置で長語計算し、単語コピーで再配置してから長語で本計算 |
| `local-reduce`, `pe-reduce`, `mab-reduce` | PE 内・MAB 内（4 PE）の縮約。PE ごとの部分和と `msl` 回転木 |
| `contraction` | 行列積。MAB の行列ユニット（gm/hm、転置読み出し、K 分割）で計算 |
| `hierarchy` | MAB・L1B・L2B をまたぐ縮約。PE 側の部分和（上の戦略のどれか）を `l1bmr`/`l2bmr`/`mvr`（DRAM・PDM）で縮約しながら運び、LM 出力なら L1BM/L2BM から戻す。放送された入力の項を複製ユニットに分割する変種もある |
| `split` | 入力が 16 MAB に放送され出力が MAB 0 だけにある場合、出力を 16 MAB に分担させて計算し、`l1bmd`→`l1bmm` で MAB 0 に集める |
| `pairs` | 全ペア縮約 Σ_{j<k} f(x_j, x_k)（転倒数など）。対角線 d=k−j ごとに放送された複製ユニットへ割り振り、x_{j+d} を T 間接で読み、行末の外は f(x, S)=0 となる番兵 S で埋めて SPMD にし、ユニットの部分和を階層転送（PDM 経由を含む）で縮約する |
| `movement`, `gather`, `allgather` | DRAM↔LM の転送計画、T 間接の gather、L1BM 経由の MAB 間コピー |
| `generate` | 入力に依存しない出力（定数・文字列・連番）を PE で生成して DRAM に上げる。値が PE 座標のビット線形関数なら少数の命令で、そうでなければ PE マスク付き即値の表で生成する。DRAM への経路は L2B ごとの `mvp` か、`mvd` で PDM に結合して 1 本の `mvp` |
| `membership` | 小さな整数値域の所属判定 any(x == y)。LM0 に値で引く表を置き、T 間接で probe 位置をクリア → 要素をマーク → probe を読み戻す（4 値で 1 回の T ロードと 1 回のアクセス） |
| `fmtseq` | 定数のバイト列が「カウンタの 10 進表記を 1 バイトの区切りで連結し、整除性で決まるトークンを定数に置き換えたもの」と出力データから分かる場合（区切り・範囲・周期・定数・整除の法はすべてデータから推定）。各 PE が自分の 8 バイト窓を担当し、4 サイクルに連続 4 トークンを載せる。窓の桁数区間はマスク付きマージで選び、先頭トークンは線形推定、各トークンの終端位置は floor(i/m) の閉形式で求めて T に載せ、LM0 のセルに右詰めで（左へのはみ出しは所有トークンが上書きする順序で）描画してから 8 文字を詰める。ホスト側で同じ f32 演算を再現して全窓を検査し、外れる窓はマスク付き即値で補正する |

スケジューラの主な工夫: ALU が埋まっているときの単純なコピーやマスク付きマージは L1BM の折り返しレジスタ経由
（`l1bmd src $lbi` → 次の行で `l1bmd $lbi dst`）に回す。一緒に読まれる値は「同じ命令で読まれる」関係の 2 彩色で別々の GRF に
置き（マスク付きマージで記憶域を共有する値は 1 つとして扱う）、それでも同じ GRF の 2 か所を読む命令は待たずにすぐ片方をコピーする。
ALU と MAU のどちらでも同じビットになるコピー（定数文字の書き込みなど）は空いている方で発行する。T 間接アクセスは値域が分かれば
その範囲だけと依存を取る。マスクレジスタの entry が残り少ないときは、フラグを作る命令をプログラム順に置く。

命令選択の主な工夫: `frelu`（符号ビットで値か −0 を選ぶ）による比較選択、ゼロフラッシュマスクで「値か 0」の選択を 1 命令に、
XOR 型ビット置換（バイト反転・ビット反転）を `sbsl`/`ibsl`/`lbsl` 回転とマスク交換に合成、2^64 を超える中間値を
「下位ビットしか使われない」解析でラップ演算に、除算は `frsqrt`² と Newton 反復（回数は探索）、exp は範囲縮小と多項式（次数は探索）。

## 検証について

候補はすべて、契約の値域から作った複数の入力ケースで参照実行と比較する（出力型への丸め込み後の値と atol で判定）。
有限の小さな値域は網羅入力と独立ランダム入力を交互に使う（網羅だけだと「全要素が含まれる」ような退化が起きるため）。
これは形式証明ではない。近似を使う候補は検証ケースを 8 に増やし、誤差が許容値の 8 割を超えるものは採用しない。

## 正直な注記・制限

- fizzbuzz は `fmtseq`（出力バイト列から「区切りで連結した 10 進カウンタ＋整除で決まる定数トークン」を推定して描画するイディオム）
  で生成する。推定できない一般の定数バイト列は、従来どおり PE マスク付き即値の表になる（32KB なら 8000 行超）。
- 符号ビット判定（`frelu`）を `x >= 0` に使うので、入力が −0.0 のときだけ `x >= 0` と異なる値を出しうる（値域の他の点では一致）。
- 浮動小数の定数は f32 に丸めて使う（誤差は検証で確認）。
- コンパイル時間は問題により数秒〜10 分程度（多数の候補を作って検証するため）。
- 参照解の一部（例: plus-two）は公式テストケースの入力値に依存した並べ替えで短くしており、そのような最適化はしない。

## ベンチマーク

`python3 -m mncompile.bench.run --output <dir>` で 73 問（original Challenge 25 問、MNIST 特設 48 問）を
コンパイルし、公式ジャッジで判定する。カーネルのソースは `benchmarks/challenge/*.py`, `benchmarks/mnist/*.py`、
問題文に書かれた追加の値の制約は `benchmarks/constraints.json`。
ランナーは問題ごとにワーカープロセスを起動し、空きメモリが全体の 12% を割ると最大のワーカーを止めて最後に単独で再実行する
（WSL ではメモリ枯渇で VM ごと落ちるため）。並列数の既定値はメモリ量から決まる。
生成した VSM と各問題のレポートは `benchmarks/results/` に保存している（下表はその `progress.json` から
`python3 -m mncompile.bench.report mncompile/benchmarks/results --readme mncompile/README.md` で生成）。

<!-- RESULTS -->

公式ジャッジで 73/73 問 Accepted。参照解（公開されている最短の Accepted 提出、MNIST は問題ページの Top）以下の行数は 19 問。Accepted 問題の行数合計は生成 1617 行 / 参照解 1077 行。

| 問題 | 判定 | 生成行数 | 参照解 | 比 | 戦略 |
| --- | --- | ---: | ---: | ---: | --- |
| 1.plus-one | Accepted | 2 | 2 | 1.00 | local |
| 2.plus-two | Accepted | 7 | 5 | 1.40 | local |
| 3.a-plus-b | Accepted | 6 | 6 | 1.00 | local/-staged |
| 4.mul7 | Accepted | 10 | 6 | 1.67 | local |
| 5.abs | Accepted | 23 | 13 | 1.77 | local |
| 6.fadd-mul | Accepted | 18 | 14 | 1.29 | local |
| 7.mul2 | Accepted | 13 | 9 | 1.44 | local |
| 8.fle | Accepted | 9 | 4 | 2.25 | local |
| 9.transpose-addr | Accepted | 16 | 10 | 1.60 | local |
| 10.gather-easy | Accepted | 12 | 6 | 2.00 | gather |
| 11.square-sum | Accepted | 21 | 11 | 1.91 | hierarchy/split-MAB+L1B:l1bmr16/l2bmr/l2bmb/l1bmm2+local |
| 12.convert-endian | Accepted | 6 | 3 | 2.00 | local |
| 13.mod3 | Accepted | 15 | 8 | 1.88 | local |
| 14.mat-sq | Accepted | 12 | 10 | 1.20 | contraction/hm-t |
| 15.contains | Accepted | 60 | 20 | 3.00 | hierarchy/l1bmr16/l1bmp2+pe+rot-membership/zero-init |
| 16.count-up | Accepted | 43 | 21 | 2.05 | generate/spread-pdm |
| 17.transpose-mab | Accepted | 45 | 15 | 3.00 | allgather |
| 18.inversion-small | Accepted | 30 | 9 | 3.33 | pairs/l1bmr16/l1bmm2+base |
| 19.inversion | Accepted | 76 | 31 | 2.45 | pairs/l1bmd/l2bmr/pdm/l2bmb/l1bmd+base |
| 20.fizzbuzz | Accepted | 103 | 98 | 1.05 | fmtseq/render-pdm/0p |
| 21.hello-world | Accepted | 13 | 9 | 1.44 | generate/spread |
| 22.bit-reverse | Accepted | 32 | 10 | 3.20 | local |
| 23.fizzbuzz-pe | Accepted | 12 | 9 | 1.33 | local |
| 24.log2 | Accepted | 15 | 7 | 2.14 | local |
| 25.hsv2rgb | Accepted | 32 | 12 | 2.67 | local |
| 1.a-b | Accepted | 4 | 3 | 1.33 | local |
| 2.fmul7 | Accepted | 5 | 5 | 1.00 | local |
| 3.relu | Accepted | 2 | 2 | 1.00 | local |
| 4.relu-grad | Accepted | 3 | 3 | 1.00 | local |
| 5.addcol-vec | Accepted | 4 | 4 | 1.00 | local |
| 6.subrow-vec | Accepted | 35 | 24 | 1.46 | split/local |
| 7.sumcol-mini | Accepted | 4 | 4 | 1.00 | local |
| 8.sumcol | Accepted | 12 | 9 | 1.33 | hierarchy/l1bmm@32/l2bmr/mvr+local |
| 9.sumrow-mini | Accepted | 9 | 6 | 1.50 | pe-reduce |
| 10.sumrow | Accepted | 24 | 20 | 1.20 | split/mab-reduce/pe+rot-local |
| 11.maxrow | Accepted | 24 | 21 | 1.14 | split/mab-reduce/pe+rot-local |
| 12.divrow-vec | Accepted | 56 | 29 | 1.93 | split/local/newton2 |
| 13.exp-low-prec | Accepted | 20 | 14 | 1.43 | local/exp_degree3 |
| 14.exp | Accepted | 30 | 21 | 1.43 | local/exp_degree6 |
| 15.onehot-mini | Accepted | 17 | 7 | 2.43 | relayout/base |
| 16.onehot | Accepted | 44 | 24 | 1.83 | split/local/base |
| 17.dram-dl-256-16 | Accepted | 5 | 5 | 1.00 | movement |
| 18.dram-ul-256-16 | Accepted | 6 | 6 | 1.00 | movement |
| 19.dram-dl-256-16p | Accepted | 25 | 19 | 1.32 | movement |
| 20.dram-ul-256-16p | Accepted | 16 | 10 | 1.60 | movement |
| 21.dram-dl-256-16-l2b | Accepted | 14 | 12 | 1.17 | movement |
| 22.dram-dl-1024-16 | Accepted | 10 | 8 | 1.25 | movement |
| 23.dram-dl-256-1024 | Accepted | 74 | 69 | 1.07 | movement |
| 24.dram-dl-16 | Accepted | 5 | 5 | 1.00 | movement |
| 25.dram-ul-16 | Accepted | 5 | 5 | 1.00 | movement |
| 26.dram-dl-16-1024 | Accepted | 44 | 40 | 1.10 | movement |
| 27.dram-ul-16-1024 | Accepted | 18 | 13 | 1.38 | movement |
| 28.dram-dl-16-16 | Accepted | 12 | 11 | 1.09 | movement |
| 29.dram-ul-16-16 | Accepted | 13 | 9 | 1.44 | movement |
| 30.dram-dl-256 | Accepted | 11 | 11 | 1.00 | movement |
| 31.dram-ul-256 | Accepted | 9 | 12 | 0.75 | movement |
| 32.matmul-trb-mab-lm-4-8-8 | Accepted | 4 | 4 | 1.00 | contraction/gm-direct |
| 33.matmul-trb-mab-lm-4-8-16 | Accepted | 7 | 7 | 1.00 | contraction/gm-direct |
| 34.matmul-trb-mab-lm-4-16-8 | Accepted | 6 | 7 | 0.86 | contraction/hm |
| 35.matmul-trb-mab-lm-4-16-16 | Accepted | 6 | 12 | 0.50 | contraction/hm |
| 36.matmul-trb-pkg-lm-256-16-16 | Accepted | 12 | 12 | 1.00 | contraction/gm-direct |
| 37.matmul-trb-mab-lm-32-8-16 | Accepted | 21 | 17 | 1.24 | contraction/gm-direct |
| 38.matmul-trb-pkg-lm-256-128-16 | Accepted | 48 | 23 | 2.09 | hierarchy/l1bmr32/l1bmm2+contraction/gm-direct |
| 39.matmul-trb-pkg-lmdram-256-1024-16 | Accepted | 38 | 29 | 1.31 | hierarchy/l1bmr32/l2bmr/mvp+contraction/gm-direct |
| 40.matmul-notr-mab-lm-4-8-8 | Accepted | 7 | 7 | 1.00 | contraction/gm |
| 41.matmul-notr-mab-lm-4-16-16 | Accepted | 23 | 13 | 1.77 | contraction/gm |
| 42.matmul-notr-pkg-lm-256-16-16 | Accepted | 23 | 13 | 1.77 | contraction/gm |
| 43.matmul-tra-mab-lm-8-8-8 | Accepted | 10 | 8 | 1.25 | contraction/gm |
| 44.matmul-tra-mab-lm-16-8-16 | Accepted | 26 | 17 | 1.53 | contraction/gm |
| 45.matmul-tra-mab-lm-16-4-16 | Accepted | 20 | 16 | 1.25 | contraction/gm |
| 46.matmul-tra-pkg-lmdram-16-256-16 | Accepted | 31 | 26 | 1.19 | hierarchy/l1bmm@32/l2bmr/mvr+contraction/gm |
| 47.matmul-tra-mab-lm-16-32-8 | Accepted | 50 | 17 | 2.94 | contraction/gm |
| 48.matmul-tra-pkg-lmdram-16-256-1024 | Accepted | 94 | 70 | 1.34 | hierarchy/l1bmd/l2bmd/mvr-pdm+contraction/gm |
