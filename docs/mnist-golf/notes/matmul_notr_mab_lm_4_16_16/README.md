# matmul_notr_mab_lm_4_16_16 — 12 行化の試行（結論: 12 行は不可、13 行が下限）

現行最短: `problems/41.matmul-notr-mab-lm-4-16-16/answer.vsm`（13 行、ACCEPTED, score=13）。
本ディレクトリは「13 行を 1 行下回る」ための試行と、その不可能性の根拠を残すもの。
**12 行で ACCEPTED になる候補は作れなかった**（best_lines=13, path=""）。

## 検証済みの候補（すべて 12 行）

| file | アイデア | 結果 |
|---|---|---|
| `cand1_merge_mauf.vsm` | 既存 cand8。`gmfma` と `l1bmm@2 $mauf $lbi` を同一行に融合 | 32/64 正解。右半分だけ不一致 |
| `cand2_merge_grf.vsm` | `gmfma ... $ln0v4 $lr0v` と 2 dst 書き込みにし、同一行の `l1bmm@2 $lr0v` で回収 | 32/64 正解（右半分は**旧 GRF0 の値**＝A 左 BF データ） |
| `cand3_merge_lm1.vsm` | `gmfma ... $ln0v4` と同一行の `l1bmm@2 $ln0v4` で回収 | 32/64 正解（右半分は **0**。旧 LM1 を読んでいる） |
| `cand4_merge_turnaround.vsm` | `l1bmm@2 $mauf $lbi; l1bmm $lbi $ln2v4` を同一行に融合 | asm error: `Reg->L1BM operation must precede L1BM turnaround.` |
| `cand5_merge_l1bmp.vsm` | 回収と放送を `l1bmp` で同一行に融合 | asm error: `L1BM forwarding happens only when Broadcast MAB16/MAB4 or Distribute is used.` |

再検証コマンド（リポジトリルート）:

```bash
python3 problems/run_problem.py 41.matmul-notr-mab-lm-4-16-16 \
  --solution scratch/mnist_golf2/matmul_notr_mab_lm_4_16_16/cand1_merge_mauf.vsm
```

13 行ベースライン（`cand0_baseline` 相当）は ACCEPTED score=13 のまま。

## なぜ cand8 の右半分は「同一行で」直せないか（実測）

`l1bmm@2` が読む PE オペランドは、同一ステップに書かれた値を見ない。
エミュレータ/アセンブラで以下を確認した。

1. `$mauf` は「直前ステップの MAU 出力」。同一行で `gmfma` の結果を読むと 1 つ前（`gmmul` の k=0..7 部分和）が返る（cand1）。
2. `gmfma` の dst に GRF0 を追加して同一行で `l1bmm@2 $lr0v` しても、読めるのは**旧 GRF0**（cand2）。
3. `gmfma` の dst を LM1 にして同一行で `l1bmm@2 $ln0v4` しても、読めるのは**旧 LM1**（cand3、右半分が 0）。
   つまり LM/GRF の「同一ステップ read は新値を読む」は同一命令内の話で、
   別命令（MAU→L1BM）間のフォワーディングには効かない。
4. 回収（PE→L1BM, `$lbi`）と放送（L1BM→PE, `$lbi`）の同一行発行は
   `Reg->L1BM operation must precede L1BM turnaround` でアセンブラが拒否（cand4）。
   折り返しレジスタでも同一ステップは不可で、最低 1 ステップ必要。

## 12 行が不可能な理由（スケジュール下界）

13 行解の構造は次の 4 フェーズ。

```
step 0      : lpassa $mabid $t            (T 設定, ALU)
step 1      : gbfn $lm0v4 $lr0v           (A 左 BF, ALU, LM0 読み)
steps 2..9  : mwrite 8 回                  (B ロード 4 + 転置書き 4, 各 32 値)
step 9      : gmmul (最後の mwrite と同居)
step 10     : gmfma                        (右半分完成, y=$mauf)
step 11     : l1bmm@2 $mauf $lbi           (MAB2 から回収)
step 12     : l1bmm $lbi $ln2v4            (全 MAB へ放送)
```

- **mwrite は 1 ステップ 1 本**（SDM 3.6.4 の mau-mwrite グループ制約）。
  B^T を 2 面 × 2 MAB 分（= 4 ブロック 64 値×4）埋めるには、
  ロード 4 本 + 転置書き 4 本 = **8 本の mwrite が情報量的に必須**。
  各 mwrite は 4 サイクル × 8 値 = 32 値しか書けない。
- **T は step 0 に書く必要がある**。T 書き→T 間接読みは 7 サイクル（= 2 ステップ）必要で
  （`Res::T` の DataRace ルール、実測でも step 0 書き→step 1 読みは DataRaceError）、
  T 依存の B ロードは step 2 が最早。
- **A の BF は隙間に入るだけでボトルネックではない**。A の gbfn は LM0 を読むため
  B ロード（LM0 読み）と同一ステップには置けない（`lm0` と `in_lm0` の field conflict を実測確認）。
  A 左 BF は step 1、A 右 BF は step 9（転置書きは `$aluf` 読みなので LM0 競合なし）に入る。
  step 1 は T 依存の書き込みには使えない（T 書き step 0 → 読み step 2 のため）ので、
  A の BF を消しても行数は減らない。
- 以上より 8 本の mwrite は step 2..9 を占める。$ly の最後の転置書きが step 9 なので
  **gmfma は step 10 が最早**（行列書き→MAU は「直後のステップから」）。
- 回収は「直前ステップの MAU 出力」しか読めないので **step 11 が最早**。
- 放送は回収の翌ステップが最早（上記 3.6.8 の制約）で **step 12**。

したがって 13 ステップ = 13 行が下限で、どこか 1 フェーズを削らないと 12 行にならない。
削れる候補は次の 4 つだが、いずれも不可能:

1. **T 設定の削除** — per-MAB に別データを与える手段は T/BAR のみ。
   BAR も step 0 書き→step 1 読みで `PortConflictError`（実測）。LM1 は T 間接不可。
2. **mwrite を 7 本に** — 4 ブロック × (ロード + 転置書き) は 8 本。
   1 命令で 2 行書けるのは half の `hmwrite ll` だけだが、
   g 行列の物理行は 2 行/サイクルにならず（g は 4 行/命令のまま）、かつ
   gbfn の g 出力は LSB 側 1 長語が 0 なので 2 行分のデータを作れない。
3. **A 左 BF を他のステップに融合** — 上記の LM0 競合で不可能。
4. **回収/放送の融合** — cand4/cand5 の通りアセンブラが拒否。

## 検討して捨てた別路線

- **half 精度 (`hbfn/9` + `hmread` + `hmmul`)**: 転置が 2 命令で済み 6〜8 行になるが、
  B の値が最大 1515 で BF-half（仮数 9 bit）では 4 刻みに丸められ、
  誤差 ~1e2〜1e3 で atol=1e-5 を満たさない（`../mnist_golf/.../README.md` の既存検証）。
  `hbfn` は `/n` が必須（実測: `hbf needs significand-bit parameter`）で、
  11 bit 仮数の plain half は使えない。BF のブロックは 16 半語で、
  転置後は行内の指数差が大きく丸めがさらに悪化する。
- **A を matrix にする向き**（転置不要）: 出力添字が C の列でなく行になり、
  PE への分配 `dst[2p],dst[2p+1]` が要求レイアウト（C は列 2p,2p+1）と一致しない。
  出力の転置が別途必要になり行数は増える。
- **T を使わない 2 ラウンド方式**: 1 MAB で 4 ブロックすべてを扱うとロード 8 + 転置書き 8 = 16 mwrite。
- **テストケース依存の代数短縮**（B[i][j]=100i+j なので C=100·S1⊗1 + S0⊗v）:
  厳密には成立するが、この問題の一般解ではなく、再ジャッジで無効になり得るため採用しない。

## 参考ファイル

- `probe.py` / `probes/`: エミュレータ直叩きの検証スクリプト（T の間接参照、mwrite の
  アドレス写像、gbfn の出力、同一ステップ read の挙動など）。
- `../mnist_golf/matmul_notr_mab_lm_4_16_16/`: 前回探索の候補・ノート。
