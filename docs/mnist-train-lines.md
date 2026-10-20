# MNIST 学習 VSM を行数削減で 500 行まで持っていく作業メモ

対象: `viz/core/benchmarks/mnist_train_step.vsm`（`fx_export` が生成する 1 学習ステップ）。

**目標の 500 は命令行数（コメントと空行を除く）を指す。** raw 行数はオペレーションごとの
コメント（1 オペレーションあたり 6 行前後）を含むため、命令 500 行でも raw は 1,000 行前後になる。

行数は 2 通りで数える。

- **raw 行数**: `wc -l`。コメント・空行を含む。コミットメッセージの数字はこちら。
- **命令行数**: コメントと空行を除いた行。1 行が 1 VLIW スロット。以下の内訳はこちら。

## 現在地（2026-10-20）

- raw: **2,186 行**
- 命令: **1,503 行**（`gpu_coverage` の PE 行は 1,018、MV 文 144）

| 種別 | 命令行 |
| --- | ---: |
| DL（DRAM→LM） | 689 |
| UL（LM→DRAM） | 342 |
| Gemm | 238 |
| ReduceSum | 39 |
| SGDUpdate | 36 |
| Sub | 30 |
| Div | 30 |
| OneHot | 25 |
| ReduceMax | 21 |
| Exp | 17 |
| Add | 12 |
| Mul | 9 |
| Identity | 8 |
| Greater | 4 |
| Relu | 3 |
| **合計** | **1,503** |

転送（DL+UL）だけで 1,031 行、全体の 69%。

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

検証（すべて手元で再実行可能）:

1. `assemble3 --instruction-mode flat` が rc=0（ハザードなし）。
2. 実データ 1 step の CPU 実行で、**8 個のパラメータ出力が旧プログラムと完全一致**。
   - 学習率を旧プログラムの値に揃えた比較で、`grad_*` と `updated_*` の合計 4,192 ワードが 0 差分。
   - 学習率を揃えないと、再エクスポートのたびに `lr_estimate` が下位ビットで変わるため
     更新後の値が数 100 ワードずれる（後述の注意）。
3. `gpu_coverage`: 1,503 行すべて GPU バックエンドが対応（未対応 0）。

## 500 行までの見通し

残り 1,003 命令。内訳は上表のとおりで、**転送 1,031 行**が依然として本体。

### 効きそうな順

1. **UL→DL の往復を消す（現状 22 組・565 行）**
   - 直前の UL が書いたテンソルを次の DL が同じ形で読み直す組。
   - 単純な LM→LM コピーでは置換できないことを実験で確認した。UL の L1BM ブロックと
     DL が期待する L2BM/DRAM 像は同じではなく、`mvp` の PDM 経由のレイアウト変換が要る
     （`docs/shortening_techniques.md` の 4.3 と同じ理由）。
   - したがって、オペレータを跨いで LM に値を残す（アドレスをパラメータ化する）方向が本命。
     ただし問題の 1 位解カーネルは入力アドレスを固定で書いているので、そのままでは使えない。
2. **オペレータ融合で往復を消す（1 組あたり 20〜100 行）**
   - SGD 更新でやったのと同じ方法。次は softmax 鎖
     （`ReduceMax → Sub → Exp → ReduceSum → Div` の 5 組、約 250 行）。
   - 続いて ReLU マスク鎖（`Greater → Cast → Mul`）と、forward の `Gemm → Add → Relu`。
   - 融合は「1 オペレータの中で LM の中間値を使う」ので、レイアウト変換の問題を踏まない。
3. **残りの計算カーネル（約 450 行）**
   - Gemm 238（5 個）、ReduceSum 39、Sub 30、Div 30、OneHot 25、ReduceMax 21、Exp 17。
   - 1 位解と比べてまだ大きいもの（`grad_fc1_weight_gemm` など）を寄せる。

### 粗い見積り

| 段階 | 命令行 |
| --- | ---: |
| 現在 | 1,503 |
| softmax 鎖の融合 | 約 1,250 |
| ReLU マスク・forward 鎖の融合 | 約 1,100 |
| 残りの UL→DL 往復の除去 | 約 850 |
| 計算カーネルのゴルフ | 約 750 |
| 500 | さらに 250 行。出力仕様（勾配 4 本を書かない）か、データ配置の変更が要る |

500 は「カーネルを差し替える」範囲では届かない。転送の除去と出力仕様の見直しまで含める必要がある。

### 次の一手

1. softmax 鎖を 1 オペレータに融合する。`Softmax` ノードは export で分解されているので、
   分解後の `ReduceMax/Sub/Exp/ReduceSum/Div` を `fuse_softmax` パスで 1 ノードに戻し、
   LM 内で計算するカーネルを書く。
2. そのために、`Div`/`Sub` の 1 位解カーネルを「入力アドレス可変」で呼べるようにする
   （現在は `$lm0v` などを固定で埋め込んでいる）。

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
