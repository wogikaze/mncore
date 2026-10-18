# 10 — 53行設計（現時点の最良仮説）

## 数値目標
- 53行 = PE 51行 + MV 2行。
- 1行に ALU 1 + MAU 1 + L1BM 1 + L2BM 1 まで同居可能（相互に独立なら）。
- したがって **ALU ≤ 51 かつ MAU ≤ 51** が条件。現状 ALU 66 / MAU 41。

## 63行を切るための変換（優先順）
1. **ALU imm を MAU 生成へ**: imm 24本のうち float 系を fvfma/fvadd で作る。
   - 0.01 = 0.1*0.1、0.001 = 0.01*0.1（MAU 2本、ALU 2本を削減）
   - 障害: 置き場の GRF0 ポート衝突（L35/37/42/49/51 すべて不可、実測済み）。
   - 回避案: `fvpassa` で 0.1 を GRF1 に複製してから GRF1 同士で乗算する。
     その複製自体は L1BM/MAU 行に載せられる可能性がある。
2. **mod 15 テーブル**: Fizz/Buzz 判定を lsub 連鎖（6 ALU）から
   「n mod 15 を float で計算（2〜3 MAU）+ L1BM の15エントリ表読み（1 L1BM）」へ。
   - 表は 15×4bit。`imm` 4本＋`l1bmd` 1本で構築可能。
   - canvas 側は「field の長さと文字種」を表から引く形に再設計。
3. **canvas の L1BM 化**: 現在 LM0 に 16バイトを書いている部分を L1BM に置き、
   `l1bmd` の T 間接読みで pack を 2〜3 ALU に短縮。
4. **座標構築**: 7-サイクル置換は固定。9 ALU が下限（生成器は17で不可）。

## 検証手順
```
assemble3 --instruction-mode flat < cand.vsm  # hazard
python3 fastsim.py cand.vsm                   # mism==0
python3 problems/run_problem.py challenge/20.fizzbuzz --solution cand.vsm
```

## 現実的な到達点
- 変換1だけで ~64行。
- 変換2+3で ~55行。
- 残り2行は pack/座標の微減。
- どこかで必ず「MAU の置き場」問題に当たるため、ALU/MAU のレジスタバンクを
  最初から分けて設計し直す必要がある（ALU は GRF0、MAU は GRF1 中心）。
