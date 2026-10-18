# 48問の改善可否一覧（2026-10-19）

判定の意味:
- **A**: ハードウェア規則（ポート衝突・ハザード距離・資源数）と資源数え上げによる強い構造的主張。形式証明ではない。
- **B**: 少数〜十数個の候補を作り、依存鎖・制約から「これ以上は無理」と主張。網羅列挙ではない。
- **C**: 改善候補が作れなかっただけ（下限の主張なし）。
- **更新**: 我々が X を更新した問題。

| # | 問題 (slug) | X | 判定 | 根拠の要点 |
|---|---|---|---|---|
| 1 | mat_sub | 3 | A | fvadd は 8語/step、LM0 は1命令1領域、A/B 同時読み不可、退避は DataRace |
| 2 | mul_const | 5 | A | fvmul 1LW/cycle で4命令、7.0 の imm は LM0 と同時発行不可 |
| 3 | relu | 2 | A | 1命令で扱えるのは4長語まで、16 float を1命令で書けない（公式Topも2） |
| 4 | relu_grad | 2 | 更新 | hvpassa マスク + zero + imm 1.0（dirty 対応） |
| 5 | add_colvec | 2 | 更新 | hvadd 半精度加算（±512 は正確） |
| 6 | sub_rowvec | 24 | C | 23行案は dirty 非対応で撤回。現X 24 は syttrea |
| 7 | sum_col_mini | 4 | B | 3行候補10本不合格。4項加算に2サイクル必要 |
| 8 | sum_col | 8 | 更新 | 2長語 l1bmr4ffadd + l2bmrffadd + mvrffadd |
| 9 | sum_row_mini | 6 | B | 5行化不可。fvpassa→fvadd→gbfn→gmwrite→gmmul→msr の直列6段 |
| 10 | sum_row | 16 | B | 15行は混合精度で誤差 1.3〜1.45e-4、4パス+ギャザで16行 |
| 11 | max_row | 20 | B | 19行候補9本不合格 |
| 12 | div_row | 29 | B | 28行候補8本不合格（BAR/GRF1 ハザード） |
| 13 | exp_lowprec | 9 | 更新 | 5次多項式 half FMA + 厳密 x の単精度 FMA |
| 14 | exp | 16 | B | 15行候補は GRF 1ステップハザードで不可 |
| 15 | onehot_mini | 7 | B | 6行不可（LM1 二重出力・ixor の2bitマスク・imm/LM0 同時不可） |
| 16 | onehot | 24 | B | 23行候補8本不合格 |
| 17 | dram_dl_256_16 | 5 | A | 1MVで2L2Bに別データ不可(m≥2)、L2BM→L1BM→PE で j≥3 |
| 18 | dram_ul_256_16 | 6 | A | PE→L1BM→L2BM 10cyc で j≥4、MV2 |
| 19 | dram_dl_256_16p | 19 | A | LM0 8語/step×16step+MV1。18行は最終チャンク6長語不足 |
| 20 | dram_ul_256_16p | 10 | A | T設定2+7cyc規則+l1bmm2+l2bmd2+MV1。9行不可 |
| 21 | dram_dl_256_16_l2b | 12 | A | mvp2 + j10（l2bmb4+l1bmm8）の下限 |
| 22 | dram_dl_1024_16 | 8 | A | MV2 + PE5（l2bmd4+l1bmm4）の下限 |
| 23 | dram_dl_256_1024 | 68 | A | l2bmd64 + MV2 + l1bmd + 6cyc規則。67行候補は DataRace/不一致 |
| 24 | dram_dl_16 | 4 | 更新 | mvb DRAM→L2BM 直接放送（ゼロ初期化前提を排除できない点に注意） |
| 25 | dram_ul_16 | 4 | 更新 | L1BM 宛先ずらしで nop 削減 |
| 26 | dram_dl_16_1024 | 39 | A | l2bmd32 + MV5 + l1bmd4 + 7cyc。38行は1024値不一致/DataRace |
| 27 | dram_ul_16_1024 | 13 | A | l2bmd4 + MV2 + T設定 + ハザード。12行不可 |
| 28 | dram_dl_16_16 | 7 | 更新 | mvb/n128 + l2bmb + flat l1bmm×4 |
| 29 | dram_ul_16_16 | 8 | 更新 | T=8·l2bid + l2bm@0 + mvp/n64 |
| 30 | dram_dl_256 | 10 | A | ALU 6書き込み + 転送 + MV。9行不可 |
| 31 | dram_ul_256 | 7 | A | T設定 + 7cyc + 11cyc + MV。6行不可 |
| 32 | matmul_trb_mab_lm_4_8_8 | 4 | A | gmwrite 4行/命令、同一面で mwrite+gmmul 不可、ALU 1/step |
| 33 | matmul_trb_mab_lm_4_8_16 | 6 | 更新 | hbfn + hmwrite + hmmul（半精度16次元） |
| 34 | matmul_trb_mab_lm_4_16_8 | 6 | B | 5行候補10本不合格（readh mau 衝突等） |
| 35 | matmul_trb_mab_lm_4_16_16 | 6 | B | 5行不可（hbfn 5個の依存） |
| 36 | matmul_trb_pkg_lm_256_16_16 | 6 | B | 5行不可（hmwrite 4回+BF供給） |
| 37 | matmul_trb_mab_lm_32_8_16 | 17 | A | T=8*mabid を1命令で作れず、BAR 併用は PortConflict |
| 38 | matmul_trb_pkg_lm_256_128_16 | 23 | B | gbfn 12本+…の列挙で23行 |
| 39 | matmul_trb_pkg_lmdram_256_1024_16 | 29 | B | gmmul16 + ALU12 + tail の列挙で29 |
| 40 | matmul_notr_mab_lm_4_8_8 | 7 | B | ロード→転置→BF→gmmul の依存鎖で7 |
| 41 | matmul_notr_mab_lm_4_16_16 | 13 | B | T書き2step + mwrite8本の依存鎖で13 |
| 42 | matmul_notr_pkg_lm_256_16_16 | 10 | 更新 | 半精度16次元内積 + lpassa $mreadf 転置 |
| 43 | matmul_tra_mab_lm_8_8_8 | 8 | B | B転置6行 + gmmul2行で8 |
| 44 | matmul_tra_mab_lm_16_8_16 | 15 | B | GRF 2step + 放送で15 |
| 45 | matmul_tra_mab_lm_16_4_16 | 14 | 更新 | ゼロ初期化利用のセットアップ削減 |
| 46 | matmul_tra_pkg_lmdram_16_256_16 | 22 | 更新 | mvrffadd/n128 で MV 5→1 |
| 47 | matmul_tra_mab_lm_16_32_8 | 17 | B | T 値2種類が必要で17 |
| 48 | matmul_tra_pkg_lmdram_16_256_1024 | 61 | B | 末尾38語 + 先頭23歩で61 |

集計: 更新12、A 16、B 19、C 1。
