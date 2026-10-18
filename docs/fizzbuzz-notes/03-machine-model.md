# 03 — マシンモデル実測と 53 行への道筋

## 実測で確定した事実 (emulator dump, dump_dram.py 使用)

### 各 PE は出力ブロックを 1 個だけ産出する

- チップ構成: 8 L2B × 8 L1B × 16 MAB × 4 PE = 4096 PE。group = L2B 2 個 (計 4 group)。
- 出力経路: PE word($s0) → `l1bmd` (PE→L1BM 結合; cycle0 列のみが実際に使用される)
  → `l2bmd $lb0 $lc0` + `l2bmd $lb32 $lc256` → `mvd/n512 $lc0 $p0@0` (全 4 group の L2BM を
  group0 PDM に結合) → `mvp/n4096` → group0 DRAM。
  - L1BM は 256 長語書かれるが使われるのは 64 長語 (cycle0 列) のみ ⇒ **PE あたり 1 長語 = 8 バイト = 1 ブロック**。
  - $s0v/1100 は $s0,$s1 を書くが $s1 は未使用 (実測: $s0 のみが出力に到達)。
- judge の `j=91 m=2`: j = PE 行数、m = MV 命令数。score = j + m。
  - **現行: PE 91 行 + MV 2 = 93。53 行には PE 行 ≤ 51 が必要。**

### PE 座標 → ブロック番号 (4096/4096 完全一致で検証済み)

```
b = (m>>1)<<9 | (h>>1)<<7 | g<<5 | c<<4 | (h&1)<<3 | (m&1)<<2 | p
```
- g = l2bid>>1 (group), c = l2bid&1 (L2B), h = l1bid (0..7), m = mabid (0..15), p = subpeid (0..3)。
- 低ニブル = (h&1)<<3 | (peid&7)、bit4-6 = l2bid<<4。
- 検証法: PE の $s0 に座標エンコード値を書いて dump (4096 全一致)。

### GRF 語内規約

- 32bit 整数 ALU 演算の結果は長語の **MSB 側 32bit** に入る (LSB 側は残存値)。実測で確認。
- 書き込みマスク `$x/1000` 等 = 単一行マスク (cycle ごとに 0/1、第 1 サイクルから)。
  - `/1100` = cycle0,1 のみ書く。`/$imrN` = 可変エントリ (動的マスク)。`imm` と LM0 アクセスは同時発行不可 (ビット共有)。

### グループ同時発行条件 (表3.6)

- ALU (imm 含む) / mau-calc / mau-mwrite / mau-mread / L1B / L2B はそれぞれ 1 命令/行。
- **imm は ALU グループ**。MAU・L1B・L2B とは併記可、他の ALU とは不可。
- nop は wait 以外と併記不可 (1 行使う)。noforward は任意と併記可。

## 現行 main.vsm のコマンド国勢調査 (93 行)

| グループ | 数 |
|---|---|
| ALU | 66 |
| MAU | 43 |
| L1B | 1 |
| L2B | 2 |
| MV | 2 |
| nop | 8 |
| noforward | 1 |

- ALU が 66 → **行数は 66 未満にできない** (ALU は 1 行 1 個)。
- 93 行 = ALU 行 66 + ALU 非搭載行 27 (nop 8, MAU 単独 ~15, L1B/L2B/MV 5)。
- **53 行の必要条件: ALU コマンドを 66 → ≤51 に削減** (MV 2 は固定)。その後、全非 ALU 命令を
  ALU 行へ載せ替え、nop を消す再スケジューリング。

## 削減候補 (優先順)

1. **L5–L13 (12 ALU)**: PE 座標 → blkid のビット集約。dmwrite/dmread (行列レジスタ転置) トリック +
   aluf フォワーディング連鎖。座標式が判明したので別構成 (iand/ilsl/ior の直接合成 ~11 命令や
   float 2^23 トリック) を再設計できる。まずここから。
2. **imm 24 個** (L2,3,14,15,18-20,22,23,26-31,34,36,48,49,52,54-56,78): 文字定数 F,i,B,u,z,\n,0x30,
   逆数 1/63,1/71,1/79,0.1,0.01,0.001 等。相互生成 (例: z=u+5, F=B+4) は ALU 1 個で置換 = 純減にならないが、
   既存 op へ折り込める場合は減る。逆数は fvfma/fvadd 連鎖の途中で生成できる可能性。
3. **位置チェーン L57–L77 (ipassa×2, ladd×5, lpassa, ior×2)**: canvas 書き込み T 位置の計算。
   $mt の flat 指定を工夫して ladd を削れる可能性。
4. **pack L79–L84 (6 ALU)**: LM0 canvas から 4 長語読んで 3×(ilsl+ior)。canvas 側の格納形式を
   変えて削れる可能性。

## 検証ループ

- `dump_dram.py <candidate.vsm>` で 4096 語を全ダンプ (~3 秒)。ベースライン期待値一致を確認済み。
- 期待値チェック: 最終語 index4095 の末尾 2 バイトは don't care。
- judge 直接: `python3 judge/judge-py/judge.py problems/challenge/20.fizzbuzz/testcase.vsm <cand>`。

## 参考: 公開情報からの構造 (angel_p_57, 5位)

- 112 行版のステージ内訳: const 20 / blkid 9 / select 5 / position 14 / canvas 2 / ftos4 15 / slide 23 / makeblk 16 / merge 8。
- 43→112 のチューニングは「処理のオーバーラップ」(passa の隙間に定数生成・L1BM 処理を埋める)。
- 社内記録 53 行の手法は非公開。当リポジトリの 93 行版は既に 112 行版より密。
