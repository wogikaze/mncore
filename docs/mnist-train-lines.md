# MNIST 学習 VSM を行数削減で 500 行まで持っていく作業メモ

対象: `viz/core/benchmarks/mnist_train_step.vsm`（`fx_export` が生成する 1 学習ステップ）。

**目標の 500 は命令行数（コメントと空行を除く）を指す。** raw 行数はオペレーションごとの
コメント（1 オペレーションあたり 6 行前後）を含むため、命令 500 行でも raw は 1,000 行前後になる。

行数は 2 通りで数える。

- **raw 行数**: `wc -l`。コメント・空行を含む。コミットメッセージの数字はこちら。
- **命令行数**: コメントと空行を除いた行。1 行が 1 VLIW スロット。以下の内訳はこちら。

## 現在地（2026-10-20）

- raw: **2,448 行**
- 命令: **1,689 行**（`gpu_coverage` の PE 行は 1,128、MV 文 168）

| 種別 | 命令行 |
| --- | ---: |
| DL（DRAM→LM） | 772 |
| UL（LM→DRAM） | 427 |
| Gemm | 238 |
| Sub | 62 |
| ReduceSum | 39 |
| Mul | 31 |
| Div | 30 |
| OneHot | 25 |
| ReduceMax | 21 |
| Exp | 17 |
| Add | 12 |
| Identity | 8 |
| Greater | 4 |
| Relu | 3 |
| **合計** | **1,689** |

転送（DL+UL）だけで 1,199 行、全体の 71%。

### 履歴

| 日付 | raw | 変更 |
| --- | ---: | --- |
| 10/19 | 4,620 | ベンチマーク初版（386597a） |
| 10/19 | 4,227 | DL/ReduceMax/SumRow を問題カーネルに（2cc5fa8, b1cdf2e） |
| 10/19 | 3,016 | OneHot/Exp/重み勾配 GEMM を問題カーネルに（f6477a9） |
| 10/20 | 3,036 | 現ソースから再生成。GEMM の行列面クリア（97c6f81）が未反映だった分 +20 |
| 10/20 | 2,488 | Div を DivRow 1 位解 29 行に置換（578 → 30 命令） |
| 10/20 | 2,448 | SubRow を 1 位解 24 行に置換（65 → 25 命令） |

## 今回の変更と検証

- `fx_export/operators/div.py`: `problems/12.divrow-vec/answer.vsm` の 29 行をそのまま埋め込み。
- `fx_export/operators/sub.py`: `problems/6.subrow-vec/answer.vsm` の 24 行をそのまま埋め込み。
- `viz/core/benchmarks/mnist_train_step.vsm`: 再生成して差し替え（GEMM クリア修正も反映）。

検証（すべて手元で再実行可能）:

1. `assemble3 --instruction-mode flat` が rc=0（ハザードなし）。
2. 実データ 1 step の CPU 実行で、DRAM 最終状態 **1,056,256 ワードが旧プログラムと完全一致**。
   - `cpu_step research/experiments/mnist-gpu <vsm>` を新旧で実行し、`cpu_final.bin` を `cmp`。
3. `gpu_coverage`: 1,689 行すべて GPU バックエンドが対応（PE 行 1,128、未対応 0）。
   - この環境には GPU が無いので、実機の `gpu_run_program` は未実行。

## 500 行までの見通し

残り 1,189 命令。内訳は上表のとおりで、**転送 1,199 行をどうするか**が本題。

### 効きそうな順

1. **UL→DL の往復を消す（最大 -733 行）**
   - 直前の UL が書いたテンソルを次の DL が同じ形で読み直す組が 26 組あり、両方で 733 行。
   - 例: `grad_fc1_weight` を UL（48 行）→ DL（47 行）→ スケール → UL（48 行）。
   - 26 組のうち **20 組は UL 側の LM レイアウトと DL 側の LM レイアウトが同一**。
     残り 6 組は DL が再レイアウトしている（`_sub`, `_exp`, `probs`, `target_onehot`, `grad_fc1`）。
   - 同一レイアウトなら、UL+DL を LM1→L1BM→LM0 のコピー（数行）に置き換えられる見込み。
     ただし長寿命の値（`grad_output` は 3 回読まれる）は、LM1:0 が後続オペレータに
     上書きされるため、コピーの置き場所か liveness を考える必要がある。
   - 各オペレータは入力 LM アドレスを `addr_in(0) == 0` のように固定アサートしているので、
     単純に UL/DL を消すだけでは消費側のアドレスと合わない。
2. **残りの計算カーネルを 1 位解級にする（-100〜150 行）**
   - Gemm 238（5 個）、Sub 62（6 個）、ReduceSum 39、Mul 31、OneHot 25、ReduceMax 21、Exp 17、Add 12。
   - 特に `grad_fc1_weight_gemm`（77 行）と `grad_fc2_weight_gemm`（63 行）は問題 48/45 の解と比べる余地がある。
3. **境界 IO の削減（-100〜200 行）**
   - 入力 6 本・出力 9 本。大きいのは fc1 重み（16×1024）の積み下ろしで、1 回 48〜77 行。
   - 学習に不要な中間出力（`grad_*_scaled`）を DRAM に書かない、勾配出力を落とす、などは
     グラフの出力仕様を変える判断が要る。

### 粗い見積り

| 段階 | 命令行 |
| --- | ---: |
| 現在 | 1,689 |
| UL→DL 往復の除去 | 約 960 |
| 計算カーネルのゴルフ | 約 850 |
| 境界 IO の削減 | 約 700 |
| 500 | さらに 200 行。出力仕様かデータ配置の変更が要る |

500 は「カーネルを差し替える」範囲では届かない。転送の除去と出力仕様の見直しまで含める必要がある。

### 次の一手

1. 同一レイアウトの 20 組のうち 1 組（例: UL 45 → DL 46）で、UL+DL を LM1→L1BM→LM0 の
   コピーに置き換える実験をする。コピーが本当に数行で済むか、シミュレータで確認する。
2. コピーで済むなら、変換器に「UL の直後に同じテンソルの DL が来たらコピーに置換」のパスを足す。
   長寿命の値は、コピーを DL の位置に置く（LM0 が生きている間だけ保持する）ことで回避できるか検証する。
3. 並行して、残っている Gemm 5 個（238 行）を問題 48/45 の解に寄せる。

## 再生成と検証の手順

```sh
# 1. ONNX を出す（乱数プローブの都合で毎回わずかに変わる。下の注意を参照）
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

# 4. 実データ 1 step を CPU で実行し、DRAM 最終状態を比較
./viz/core/target/release/cpu_step research/experiments/mnist-gpu scratch/train_step/train_step.vsm
cp research/experiments/mnist-gpu/cpu_final.bin /tmp/new_final.bin
# 旧プログラムでも同じことをして cmp する

# 5. GPU バックエンドの対応状況
./viz/core/target/release/gpu_coverage viz/core/benchmarks/mnist_train_step.vsm
```

## 注意

- **lr 定数は再生成のたびに下位ビットが変わる。** `fx_export/export.py` が
  `(update / grad).abs().mean()` で学習率を推定しており、プローブの乱数に依存する。
  今回の再生成では `0.009999952279031277`（旧ベンチマークは `0.009999953210353851`）。
  固定したいなら `learning_rate` を 0.01 に決め打ちする変更が要る。
- 旧ベンチマークは 97c6f81 の GEMM 行列面クリアを含んでいなかった。今回の再生成で反映済み。
- `research/experiments/mnist-gpu/train/train_fixed.vsm` は 100 epoch 実行時の成果物で、
  fc1 側 GEMM のクリアが入っていない。再学習するときは再生成が必要。
- GPU 実機がこの環境に無いため、`gpu_run_program` と 100 epoch の再実行は未検証。
