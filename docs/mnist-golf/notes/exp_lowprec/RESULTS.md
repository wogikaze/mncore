# exp_lowprec golf 試行結果（最終）

## 前提
- 現行 `problems/13.exp-low-prec/answer.vsm`（syttrea 作, 全体1位）= score 10 (j=10, m=0)、公式 judge で ACCEPTED。
- 目標は 9 行以下。9 行候補を 4 種作成して `run_problem.py` で検証したが、いずれも精度不足で不合格。

## 現行解の理解（シミュレータで 4096 値すべて一致を確認）
- `E = exp(x/2)` を half 精度多項式（A..D の 4 FMA）で計算し、最後だけ `E = D*y + 1`（y=x/2 を float で厳密に）→ `Y = E²`。
- 途中の値: A=0.0044·h(x)+0.042, B=A·t+0.168（0.168 は L1BM 4x4 縮約で 0.042 の 4 倍）, C=B·t+0.5, D=C·t+1.0。
- 最後の積算を厳密 y にするため、half 丸め誤差 δ=y-t が
  `δ[(exp(t)-1)/t - exp(t)]` となり t≈1 でほぼ相殺される。これが精度の鍵。
- 誤差 max 0.0075（atol=0.009、余裕 0.0015）。

## 9 行候補と検証結果（すべて score=9 だが不合格）
| file | 構造 | 結果 |
|---|---|---|
| cand1.vsm | 5 half FMA + half E + 単精度 square×2 | 4078/4096 正解、max err 0.0107 |
| cand2.vsm | cand1 と同構造・別係数 | 4081/4096 正解、max err 0.0107 |
| cand3.vsm | 4 half FMA + half E + square×2 | 4066/4096 正解 |
| cand4.vsm | 3 half FMA + 厳密 x の E×2 + square×2、b0=4a0 束縛 | 1009/4096 正解（max err 0.0256） |
| answer.vsm | 現行 10 行（参考） | ACCEPTED score=10 |

シミュレータ（float32 と MN-Core2 独自 half s1e6m9 を再現）は公式エミュレータと 4096 値で完全一致を確認済み。

## 9 行が成立しない理由
- 精度上、最後の積算 E=D·x+1（または D·y+1）は単精度が必要（MAU 単精度は 2 要素/cycle）→ 2 行。
- 二乗も単精度 → 2 行。tail で 4 行。
- 多項式は 4 次以上が必要 → half FMA 3 回（4 要素/cycle）→ 3 行。
- 合計 7 MAU + 定数設定 2 行 = 9 行が下限。
- しかし 3 half FMA 構造は定数 5 個（a1, a0, b0, b1, 1.0）が必要。行 1,2 の imm 2 個と
  L1BM 折り返し中継（4 倍のみ、書込み→放送で 2 行遅延）で賄うと b0=4a0 の束縛が避けられない。
  exp の係数比 y²/y³=3 に対し中継は 4 倍で、この束縛下の最良近似は max err 0.0256。
- その他の制約: MAU 1 命令で GRF0 は 1 オペランドのみ / imm と LM0 アクセスは同時発行不可 /
  T レジスタは書込み後 2 ステップ必要 / MAU calc は 1 ステップ 1 命令。
- half で最後の積算と二乗を行う 9 行案（cand1/2）は、h(t) と h(D) の丸めで max err 0.0107 となり
  atol 0.009 を超える（最悪入力 x=1.9364 で D の half 丸めが固定化）。

## 結論
9 行以下は達成できず。best_lines=10, path=""。
