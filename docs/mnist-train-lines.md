# MNIST 学習 VSM を行数削減で 500 行まで持っていく作業メモ

対象: `viz/core/benchmarks/mnist_train_step.vsm`（`fx_export` が生成する 1 学習ステップ）。

**目標の 500 は命令行数（コメントと空行を除く）を指す。** raw 行数はオペレーションごとの
コメント（1 オペレーションあたり 6 行前後）を含むため、命令 500 行でも raw は 1,000 行前後になる。

行数は 2 通りで数える。

- **raw 行数**: `wc -l`。コメント・空行を含む。コミットメッセージの数字はこちら。
- **命令行数**: コメントと空行を除いた行。1 行が 1 VLIW スロット。以下の内訳はこちら。
- **アセンブル後の語数**: `assemble3` の出力行数。チャレンジのスコア `j + m` と同じ数え方。
  現在は **1,618 語**（デュアルイシューの行が 2 語、`nop/3` が 3 語になるため命令行数より多い）。

## 現在地（2026-10-20）

- raw: **2,090 行**
- 命令: **1,446 行**（`gpu_coverage` の PE 行は約 1,000、MV 文 140 前後）

| 種別 | 命令行 |
| --- | ---: |
| DL（DRAM→LM） | 669 |
| UL（LM→DRAM） | 310 |
| Gemm | 237 |
| ReduceSum | 39 |
| SGDUpdate | 36 |
| Div | 30 |
| Sub | 25 |
| OneHot | 25 |
| ReduceMax | 21 |
| Exp | 17 |
| Add | 12 |
| LossGrad | 8 |
| Identity | 8 |
| ReluGrad | 6 |
| Relu | 3 |
| **合計** | **1,446** |

転送（DL+UL）だけで 979 行、全体の 68%。

### 履歴

| 日付 | raw | 変更 |
| --- | ---: | --- |
| 10/19 | 4,620 | ベンチマーク初版（386597a） |
| 10/19 | 4,227 | DL/ReduceMax/SumRow を問題カーネルに（2cc5fa8, b1cdf2e） |
| 10/19 | 3,016 | OneHot/Exp/重み勾配 GEMM を問題カーネルに（f6477a9） |
| 10/20 | 3,036 | 現ソースから再生成。GEMM の行列面クリア（97c6f81）が未反映だった分 +20 |
| 10/20 | 2,488 | Div を DivRow 1 位解 29 行に置換（578 → 30 命令） |
| 10/20 | 2,448 | SubRow を 1 位解 24 行に置換（65 → 25 命令） |
| 10/20 | 2,186 | SGD 更新の Mul+Sub を `SGDUpdate` 1 ノードに融合（DL/UL 4 組ずつ削除） |
| 10/20 | 2,167 | 不要な `nop` を 19 行削除（`tools/squeeze_nops.py`、assemble3 が通るものだけ） |
| 10/20 | 2,130 | `(probs-target)*scale` を `LossGrad` に融合（Sub の DRAM 往復を削除） |
| 10/20 | 2,090 | ReLU 逆伝播のマスクを `ReluGrad` に融合（`frelu` 1 命令 + 乗算） |

## 今回の変更と検証

### Div / SubRow の差し替え（1 回目）

- `fx_export/operators/div.py`: `problems/12.divrow-vec/answer.vsm` の 29 行をそのまま埋め込み。
- `fx_export/operators/sub.py`: `problems/6.subrow-vec/answer.vsm` の 24 行をそのまま埋め込み。

### SGD 更新の融合（2 回目）

- `fx_export/mncore_transform.py` に `fuse_sgd_update` を追加。
  `Mul(grad, lr) → Sub(param, scaled)` を `SGDUpdate(param, grad, learning_rate)` に置換する。
- `fx_export/operators/sgd_update.py` を追加。積を `$mauf` で受けて
  `fvadd param, -$mauf` を 1 命令で行うので、scaled の DRAM 往復が消える。
- DL 43 → 39、UL 23 → 19。fc1 重みだけで 100 行減（251 → 151）。

### 損失勾配と ReLU 逆伝播の融合（3 回目）

- `fuse_loss_grad`: `Mul(Sub(probs, target), scale)` を `LossGrad(probs, target)` に。
  `fvadd` の結果を `$mauf` で受けて `fvmul` するので、`(probs-target)` の中間テンソルが消える。
- `fuse_relu_grad`: `Mul(grad, Cast(Greater(x, 0)))` を `ReluGrad(grad, x)` に。
  マスクは `frelu` 1 命令で作り、そのまま乗算に流す。

検証（すべて手元で再実行可能）:

1. `assemble3 --instruction-mode flat` が rc=0（ハザードなし）。
2. 実データ 1 step の CPU 実行で、**10 個の出力（probs + 勾配 6 本 + 更新後 4 本）が
   旧プログラムと完全一致**（学習率を揃えた比較）。
   - 学習率を揃えないと、再エクスポートのたびに `lr_estimate` が下位ビットで変わるため
     更新後の値だけが数 100 ワードずれる（後述の注意）。
3. `gpu_coverage`: 1,446 行すべて GPU バックエンドが対応（未対応 0）。

### 試して駄目だったこと: UL の dmwrite/dmread を l1bmm に置換

`UL 256`（`_max` と `_sum` の書き出し、40 行）は
`dmwrite → dmread → l1bmm` で LM1 から L1BM へ移している。これを
`l1bmm@0 $ln… $lb…` の 1 命令に置き換えると 24 行減るが、`_max` は一致するのに
`_sum` の 4 ワード組の後半が化ける（`_sum` の 32 ワード中 16 ワードが不一致）。
`dmwrite/dmread` は行列レジスタ経由で 4 ワード単位の並べ替えをしており、
単純な置換では再現できない。没。

## 500 行までの見通し

残り 946 命令。内訳は上表のとおりで、**転送 979 行**が依然として本体。

### わかったこと: UL→DL はコピーではなくレイアウト変換

以前は「UL が書いたテンソルを DL がそのまま読み直しているだけ」と考えていたが、違う。
オペレータごとに LM のレイアウトが違い、境界の DL が `mvp`/`l2bmd`/`l2bmb` で
L2B 複製を作り直している。例:

- `Exp` の出力 `_exp`: `((8_L2B:1, 4:2, 8_L1B:1), (2:1, 4_PE:1, 2_W:1))`、len=16
- `Div` が読む `_exp`: `((4_L2B:2, 64:2), (2:1, 4_PE:1, 2_W:1))`、len=256

同じ [256,16] でも LM 上の配置が違い、その変換が DL の仕事になっている。
実験でも確認した。

- UL+DL を LM1→L1BM→LM0 のコピーに置換 → 1,056,256 ワード中 5,993 ワードが不一致。
- UL の mvp と DL の mvp を L2 往復に置換 → 同じく 5,993 ワード不一致。

つまり往復を消すには、オペレータ間でレイアウトを揃える（またはオンチップで
再レイアウトする）必要がある。これは 1 オペレータの置換では済まない。

### 効きそうな順

1. **レイアウトを揃えてオペレータを融合する**
   - 要素演算（Sub/Exp/Mul/Add/Relu/Div）を 1 つの LM レイアウトに統一できれば、
     softmax 鎖（5 オペレータ）や ReLU マスク鎖を 1 オペレータにできる。
   - softmax 鎖だけで 5 組・約 250 行。ReLU マスク鎖で約 80 行。
2. **計算カーネルのゴルフ（約 450 行）**
   - Gemm 237（5 個）、ReduceSum 39、Sub 30、Div 30、OneHot 25、ReduceMax 21、Exp 17。
   - 特に `grad_fc1_weight_gemm`（77 行）はすでに問題 48 系の詰めた実装で、余りが少ない。
3. **固定オーバーヘッドの削減**
   - 転送 1 本あたり `mvp` + `wait` + `l2bmd` + `l1bmm` で 8〜17 行。本数が多い。

### 粗い見積り

| 段階 | 命令行 |
| --- | ---: |
| 現在 | 1,446 |
| softmax 鎖の融合（レイアウト変換を挟むので要設計） | 約 1,250 |
| 計算カーネルのゴルフ | 約 1,100 |
| 残りの往復の除去（レイアウト統一の拡大） | 約 950 |
| 500 | ここからさらに 450 行。データ配置か出力仕様の変更が要る |

転送は 1 本あたり 8〜17 行の固定費が支配的で、本数を減らさない限り 1,000 行を切れない。
500 は「カーネルを差し替える」範囲では届かない。

### 次の一手

1. 要素演算のレイアウト統一を 1 組で試す。たとえば `Sub` の出力を `Exp` が読む形
   （レイアウト `((4_L2B:2, 64:2), ...)` と `((8_L2B:1, 4:2, 8_L1B:1), ...)` の変換）を、
   `Exp` 側を PE レイアウト対応に書き換えて消せるか確認する。
2. それが通れば softmax 鎖の融合に進む。

## 再生成と検証の手順

```sh
# 1. ONNX を出す（学習率は毎回わずかに変わる。下の注意を参照）
python3 haribote_graph_compiler.py export scratch/train_step --example train_step --ignore loss

# 2. VSM を生成
python3 - <<'PY'
from fx_export.compile import generate_vsm_from_onnx
open('scratch/train_step/train_step.vsm', 'w').write(
    generate_vsm_from_onnx('scratch/train_step/mn_model.onnx'))
PY

# 3. アセンブル（ハザード検査込み）
./judge/judge-py/mncore2_emuenv/assemble3 --instruction-mode flat \
  < scratch/train_step/train_step.vsm > /dev/null

# 3.5 assemble3 が通る範囲で不要な nop を削る（ベンチマークに適用済み）
python3 tools/squeeze_nops.py viz/core/benchmarks/mnist_train_step.vsm

# 4. 実データ 1 step を CPU で実行し、出力テンソルを比較
./viz/core/target/release/cpu_step research/experiments/mnist-gpu scratch/train_step/train_step.vsm
cp research/experiments/mnist-gpu/cpu_final.bin /tmp/new_final.bin

# 5. GPU バックエンドの対応状況
./viz/core/target/release/gpu_coverage viz/core/benchmarks/mnist_train_step.vsm
```

## 注意

- **lr 定数は再生成のたびに下位ビットが変わる。** `fx_export/export.py` が
  `(update / grad).abs().mean()` で学習率を推定しており、プローブの乱数に依存する。
  現在のベンチマークは `0.009999435395002365`。旧ベンチマークは `0.009999952279031277`。
  新旧の出力比較をするときは、`imm` の定数を揃えてから実行する。
  固定したいなら `learning_rate` を 0.01 に決め打ちする変更が要る。
- 旧ベンチマークは 97c6f81 の GEMM 行列面クリアを含んでいなかった。現在は反映済み。
- `research/experiments/mnist-gpu/train/train_fixed.vsm` は 100 epoch 実行時の成果物で、
  fc1 側 GEMM のクリアが入っていない。再学習するときは再生成が必要。
- GPU 実機がこの環境に無いため、`gpu_run_program` と 100 epoch の再実行は未検証。
  `gpu_coverage` は全命令が対応と報告している。
