# FizzBuzz の手法を他の問題に当てた結果（2026-11-13〜）

| 問題 | 記録解 | 結果 | 最良ファイル |
|---|---:|---:|---|
| `14.exp` | 16 | **14** | `14.exp/exp14.vsm`（ACCEPTED, score=14 j=14 m=0） |
| `12.divrow-vec` | 29 | **28** | `12.divrow-vec/best.vsm`（ACCEPTED, score=28 j=28 m=0） |
| `challenge/19.inversion` | 31 | 31 | 30 語候補はハザードで不合格 |
| `27.dram-ul-16-1024` | 13 | 13 | 13 語の別解 2 つ。13 が下限と判断 |
| `39.matmul-trb-pkg-lmdram-256-1024-16` | 29 | 29 | 半精度の 23 語版は ±512 の丸めで不正解 |
| `challenge/15.contains` | 20 | 20 | 20 語の別解 1 つ |

- 並べ替えだけの探索（`tools/golfsearch.py`、20 分ずつ）は 6 問とも縮まなかった。ログは `logs/`。
- 縮んだ 2 問は計算方法と定数の置き方を変えたもの。詳細は各ディレクトリの `REPORT.md`、共通の前提は `BRIEF.md`。
- `14.exp` は許容誤差 1e-6 に対して最大誤差 9.54e-7（記録解と同じ）で、余裕が小さい。
- `problems/` の answer.vsm / answer.json はサイトへの提出記録なので変えていない。

## 第 2 波以降（提出可能 = clean と dirty の両方で公式 judge が ACCEPTED）

| 問題 | 記録 | 結果 | ファイル |
|---|---:|---:|---|
| `6.subrow-vec` | 24 | **22** | `6.subrow-vec/best.vsm` |
| `13.exp-low-prec` | 9 | **8** | `13.exp-low-prec/exp8.vsm` |
| `8.sumcol` | 8 | **6** | `8.sumcol/best.vsm` |
| `9.sumrow-mini` | 6 | **5** | `mnist-small/9.sumrow-mini/best.vsm` |
| `24.dram-dl-16` | 4 | **3** | `dram-sweep/24.dram-dl-16/best.vsm` |
| `37.matmul-trb-mab-lm-32-8-16` | 17 | **13** | `matmul-sweep/37/best.vsm` |
| `38.matmul-trb-pkg-lm-256-128-16` | 23 | **15** | `matmul-sweep/38/best.vsm` |
| `42.matmul-notr-pkg-lm-256-16-16` | 10 | **9** | `matmul-sweep/42/best.vsm` |
| `44.matmul-tra-mab-lm-16-8-16` | 15 | **10** | `matmul-sweep/44/best.vsm` |
| `45.matmul-tra-mab-lm-16-4-16` | 14 | **9** | `matmul-sweep/45/best.vsm` |
| `46.matmul-tra-pkg-lmdram-16-256-16` | 22 | **21** | `matmul-sweep/46/best.vsm` |
| `47.matmul-tra-mab-lm-16-32-8` | 17 | **14** | `matmul-sweep/47/best.vsm` |

- `10.sumrow` の 15 語版（`10.sumrow/best.vsm`）は dirty で落ちるので提出できない。dirty でも通る形では 16 語が下限と判断した。
- 縮まなかった問題（各ディレクトリの REPORT.md に理由）: 16.onehot 24, 25.hsv2rgb 12, 5.abs 13, 16.count-up 21, 11.square-sum 11, 6.fadd-mul 14,
  17.transpose-mab 15, DRAM 転送 14 問（`dram-sweep/REPORT.md`）, 行列積 9 問（`matmul-sweep/REPORT.md`）, 7.sumcol-mini 4, 15.onehot-mini 7, 2.fmul7 5, 1.a-b 3。
