# 20.fizzbuzz score 93 -> <93 検索の現状 (exhaustion catalog)

対象: `problems/challenge/20.fizzbuzz/main.vsm` (93 行, ACCEPTED score=93 j=91 m=2)
記録上の Top は 98 行 (`problem.md`)。main.vsm は著者による改良版で既に Top 超え。

## 試したこと (すべて judge で検証済み)

1. `optimize.py` nops: nop 8 個 (63,67,71,74,85,87,88,91) の削除 → 全滅。
2. `optimize.py` delete: 単独行の削除 → 全滅。
3. `optimize.py` fillnop: 単独コマンドを nop スロットへ移設 → 全滅。
4. `optimize.py` merges: 隣接ペア統合 → 全滅。
5. `optimize2.py merge/migrate/swap` (sem フィルタ + assemble3 6ms + judge 直接呼び):
   - migrate: sem-OK 34 候補すべて assemble3 で reject (field conflict / DataRace)。
     例: L56 imm → L63 nop 置換は
     `DataRaceError: racy memory read at GRF1 address 20 ... at line 56`
     (L55 `$ls20v` 書込 → L57 `$s[20,...]` 読の間の必須ギャップとして L56 が機能)
   - merge: L16-17 など semantic mismatch。
   - swap: 6 種 (L18-19, L19-20, L64-65, L68-69, L75-76, L87-88) がスコア不変で ACCEPT
     → 意味的に等価で行数は減らない (`opt2/evid/`)。

## なぜ減らないか

- 単独行とみなせるコマンドはいずれも「delay filler」か「唯一の定数生成」:
  - imm 行 (18,19,20,26,30,31,49,56,78) は近傍の GRF/LM レースギャップを兼ねる。
  - nop 8 個はすべて実ハザード (T write→read, LM0 w/r, L1BM→L2BM 距離) の必須ギャップ。
  - l2bmd (L89/90) は mvd (L92) が $lc0/$lc256 を暗黙に読むため L1BM 書き手 (L86) より後・mvd より前から動かせない。
- 併記ペアは既に実現可能な組み合わせをほぼ網羅 (著者が GRF1 移設トリックで統合済み。
  L18-20 の残りは GRF0 読 $r24v (L24) と LM0/imm 排他のため移設不能)。
- MV 2 本 (mvd/mvp) は分解不能 (L2BM→PDM→DRAM の 2 段が必要)。

## 結論

score 93 は {nop 削除, 1 コマンド移設, 隣接統合, 入れ替え} の近傍で局所最適。
これ以上の短縮は描画パイプラインの構造変更 (別アルゴリズム) が必要で、
機械的探索の範囲外。ベースラインは `attempts/baseline-93.vsm`。
