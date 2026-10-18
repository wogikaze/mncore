# MNIST 提出手順（dirty-safe 版）

- ファイル: `scratch/mnist_submit/<dir>.vsm`
- 全48ファイルを `judge.py --dirty` で検証済み（clean/dirty 両対応）。
- `record` が `new` の12問は新記録（+1点対象）。

| # | dir | slug | lines | record |
|---|---|---|---|---|
| 1 | 1.a-b | mat_sub | 3 | matches current X |
| 2 | 10.sumrow | sum_row | 16 | matches current X |
| 3 | 11.maxrow | max_row | 20 | matches current X |
| 4 | 12.divrow-vec | div_row | 29 | matches current X |
| 5 | 13.exp-low-prec | exp_lowprec | 9 | new (golf wave2) |
| 6 | 14.exp | exp | 16 | matches current X |
| 7 | 15.onehot-mini | onehot_mini | 7 | matches current X |
| 8 | 16.onehot | onehot | 24 | matches current X |
| 9 | 17.dram-dl-256-16 | dram_dl_256_16 | 5 | matches current X |
| 10 | 18.dram-ul-256-16 | dram_ul_256_16 | 6 | matches current X |
| 11 | 19.dram-dl-256-16p | dram_dl_256_16p | 19 | matches current X |
| 12 | 2.fmul7 | mul_const | 5 | matches current X |
| 13 | 20.dram-ul-256-16p | dram_ul_256_16p | 10 | matches current X |
| 14 | 21.dram-dl-256-16-l2b | dram_dl_256_16_l2b | 12 | matches current X |
| 15 | 22.dram-dl-1024-16 | dram_dl_1024_16 | 8 | matches current X |
| 16 | 23.dram-dl-256-1024 | dram_dl_256_1024 | 68 | matches current X |
| 17 | 24.dram-dl-16 | dram_dl_16 | 4 | new (golf swarm) |
| 18 | 25.dram-ul-16 | dram_ul_16 | 4 | new (golf swarm) |
| 19 | 26.dram-dl-16-1024 | dram_dl_16_1024 | 39 | matches current X |
| 20 | 27.dram-ul-16-1024 | dram_ul_16_1024 | 13 | matches current X |
| 21 | 28.dram-dl-16-16 | dram_dl_16_16 | 7 | new (golf swarm) |
| 22 | 29.dram-ul-16-16 | dram_ul_16_16 | 8 | new (golf swarm) |
| 23 | 3.relu | relu | 2 | matches current X |
| 24 | 30.dram-dl-256 | dram_dl_256 | 10 | matches current X |
| 25 | 31.dram-ul-256 | dram_ul_256 | 7 | matches current X |
| 26 | 32.matmul-trb-mab-lm-4-8-8 | matmul_trb_mab_lm_4_8_8 | 4 | matches current X |
| 27 | 33.matmul-trb-mab-lm-4-8-16 | matmul_trb_mab_lm_4_8_16 | 6 | new (golf swarm) |
| 28 | 34.matmul-trb-mab-lm-4-16-8 | matmul_trb_mab_lm_4_16_8 | 6 | matches current X |
| 29 | 35.matmul-trb-mab-lm-4-16-16 | matmul_trb_mab_lm_4_16_16 | 6 | matches current X |
| 30 | 36.matmul-trb-pkg-lm-256-16-16 | matmul_trb_pkg_lm_256_16_16 | 6 | matches current X |
| 31 | 37.matmul-trb-mab-lm-32-8-16 | matmul_trb_mab_lm_32_8_16 | 17 | matches current X |
| 32 | 38.matmul-trb-pkg-lm-256-128-16 | matmul_trb_pkg_lm_256_128_16 | 23 | matches current X |
| 33 | 39.matmul-trb-pkg-lmdram-256-1024-16 | matmul_trb_pkg_lmdram_256_1024_16 | 29 | matches current X |
| 34 | 4.relu-grad | relu_grad | 2 | new (golf swarm, dirty-safe) |
| 35 | 40.matmul-notr-mab-lm-4-8-8 | matmul_notr_mab_lm_4_8_8 | 7 | matches current X |
| 36 | 41.matmul-notr-mab-lm-4-16-16 | matmul_notr_mab_lm_4_16_16 | 13 | matches current X |
| 37 | 42.matmul-notr-pkg-lm-256-16-16 | matmul_notr_pkg_lm_256_16_16 | 10 | new (golf swarm) |
| 38 | 43.matmul-tra-mab-lm-8-8-8 | matmul_tra_mab_lm_8_8_8 | 8 | matches current X |
| 39 | 44.matmul-tra-mab-lm-16-8-16 | matmul_tra_mab_lm_16_8_16 | 15 | matches current X |
| 40 | 45.matmul-tra-mab-lm-16-4-16 | matmul_tra_mab_lm_16_4_16 | 14 | new (golf swarm) |
| 41 | 46.matmul-tra-pkg-lmdram-16-256-16 | matmul_tra_pkg_lmdram_16_256_16 | 22 | new (golf swarm) |
| 42 | 47.matmul-tra-mab-lm-16-32-8 | matmul_tra_mab_lm_16_32_8 | 17 | matches current X |
| 43 | 48.matmul-tra-pkg-lmdram-16-256-1024 | matmul_tra_pkg_lmdram_16_256_1024 | 61 | matches current X |
| 44 | 5.addcol-vec | add_colvec | 2 | new (golf swarm) |
| 45 | 6.subrow-vec | sub_rowvec | 24 | matches current X (reverted: dirty-unsafe) |
| 46 | 7.sumcol-mini | sum_col_mini | 4 | matches current X |
| 47 | 8.sumcol | sum_col | 8 | new (golf swarm) |
| 48 | 9.sumrow-mini | sum_row_mini | 6 | matches current X |

合計予想: 36×100 + 12×101 = 4812点
