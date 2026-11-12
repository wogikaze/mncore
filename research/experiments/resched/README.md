# FizzBuzz の手法を 6 問に当てた結果（2026-11-13）

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
