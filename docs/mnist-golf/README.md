# MNIST 追加問題 ゴルフ（2026-10-19）

MN-Core Challenge「Additional Problems (MNIST)」48問を対象に、全体最短 X の更新を狙った探索の記録。

## 結果

- 総合順位: **1位（Wogikaze 4817点）**（2位 syttrea 4480、3位 sosuupoyo 4448）
- 12問で X を更新し、サイト上でも我々の記録として反映済み。

| 問題 | 旧X → 新X |
| --- | --- |
| add_colvec | 3 → 2 |
| relu_grad | 3 → 2 |
| sum_col | 9 → 8 |
| dram_dl_16 | 5 → 4 |
| dram_ul_16 | 5 → 4 |
| dram_dl_16_16 | 11 → 7 |
| dram_ul_16_16 | 9 → 8 |
| exp_lowprec | 10 → 9 |
| matmul_trb_mab_lm_4_8_16 | 7 → 6 |
| matmul_notr_pkg_lm_256_16_16 | 13 → 10 |
| matmul_tra_mab_lm_16_4_16 | 15 → 14 |
| matmul_tra_pkg_lmdram_16_256_16 | 25 → 22 |

## 提出物

- `submissions/`: 48問の提出 VSM + `manifest.json` + `SUBMIT.md`。
- 全48ファイルが公式 judge の **clean / dirty 両モード**で ACCEPTED（`verify_bundle.log`, `verify_dirty2.log`）。

## 重要な知見

- judge は clean と dirty（メモリ非ゼロ初期化）の両方を実行する。
  ゼロ初期化に依存した解は dirty で落ちる。
  - relu_grad の2行解は `hvpassa` マスク + `zero $lln0v` + `imm 1.0/$limr1` で dirty 対応。
  - sub_rowvec の23行解は dirty 非対応のため24行に差し戻し。
- 残り36問はエージェントが下限を証明（`notes/` に各問題の解析）。

## 探索手法

- 第1波: 48問 × 1エージェント（workflow `mnist-golf-swarm`）。
- 第2波: 惜敗8問に絞った追撃（workflow `mnist-golf-wave2`）。exp_lowprec が9行化。
- 各候補は `problems/run_problem.py <dir> --solution <cand>` で検証。
