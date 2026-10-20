# 次の作業

## 進行中（サブエージェント）
- isa-analyst: 命令語あたりのDRAM書き込み量と語数分解
- digit-closedform: 11 ALU の T 連鎖 → 閉形式
- packer: pack 6 ALU と転送 4 語の削減
- algo-redesign: 独立アルゴリズム
- superopt: 自動局所探索
- lowerbound: 部分問題の厳密下界

## 直近の自分の結果
- `tools/fbcheck.py`（高速）、`tools/fbasm.py`（アセンブラ＋ハザード）、`tools/fbverify.py`（公式 judge、1.5 秒）
- nop 8 語はハザード上必須。埋める方向しかない。


## 2026-10-20 更新
- **下界 LB1 完了**: `research/preliminary/fizzbuzz-delivery/`（8 語 tight、系として j+m ≥ 9）。親が verify.sh を再実行して確認。
- **2 ブロック/PE の配送尾部が実測で成立**: `research/experiments/packer/probes/p12_final_2block.vsm`。
  DRAM[b]=blockA, DRAM[b+2048]=blockB が 2048/2048 ずつ一致、hazard checker rc=0。
  尾部コスト 15 j + 2 m（base +1 語）。→ レンダラを 2 ブロック対応にすれば設定コストを償却できる。
- **次の主線**: 2 ブロック/PE レンダラ。ALU 式 66 → 50 以下が 52 語の条件。

## 2026-10-20 統合（親）

### 確定した事実
1. **律速は ALU 式**（1 命令語 = 1 ALU 式）。93 語 = ALU 66 + 非 ALU 27。52 語 ⇒ ALU ≤ 50。
2. **転送・pack は床**（14 j + 2 m、置換は全て実測で失敗）。
3. **2 ブロック/PE は単独では語数を減らさない**（packer が撤回、数値で確認）。ただし「2 候補/ブロック」の
   レンダラと組み合わせた場合のみ、coords 12 + chain 16 + canvas 8 + tail 17 ≈ 53 の見積りが出ている。
4. **バイト→番号の逆変換は厳密に解ける**（0 補正、32,766 バイト全一致）が、行数は中立。
   11 ALU の T 連鎖は冗長ではなく d=2/3 の不規則 cum 表を符号化している。
5. **4 候補はほぼ必須**（4 候補必要なのは B=120/144/168 の 3 ブロックのみ）。
6. 定数 24（うち単独 imm 10 語）と座標 12 が残る最大の塊。単独 imm を MAU 行へ畳む試行は
   170 候補中 2 件しかアセンブルせず、全滅（research/experiments/parent/、hypotheses.md H1 参照）。

### 稼働中の探索
- superopt（自動局所探索）
- digit-closedform（11 ALU 連鎖の閉形式）
- twoblock（2 ブロック・2 候補レンダラの構築）

## 2026-10-20 追加（定数ルート）
- `research/experiments/constants/del_18.vsm`: **92 語、ハザードチェッカ通過、公式 judge で 22 バイトのみ不一致**
  （`32744 correct, 22 mismatch`）。失敗は DRAM word 0..2（バイト 0..23）に限定。
  原因は `imm i"32" $r25`（d=1 領域の閾値）の削除。→ これを別手段で生成できれば 93→92 の初改善。
- `del_76.vsm` は 92 語で 209 不一致。
