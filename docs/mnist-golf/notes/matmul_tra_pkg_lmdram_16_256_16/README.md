# matmul_tra_pkg_lmdram_16_256_16 golf

現行の全体最短 `problems/46.../answer.vsm` は 25 行（j=20, m=5）。
ここでは MV 命令を 5 語から 1 語に減らし、**22 行（j=21, m=1）** まで縮めた。

## 候補

| file | lines | score (j+m) | 概要 |
|---|---|---|---|
| `cand1.vsm` | 22 | 22 (j=21, m=1) | 最良。L1BM の行配置を 16 長語単位で組み替え、`mvrffadd/n128` 1 語で 4 group 分の DRAM を書く |
| `cand2.vsm` | 22 | 22 (j=21, m=1) | l1bmm 4 語版（GRF ハザード回避の nop を 1 行使う） |
| `cand3.vsm` | 22 | 22 (j=21, m=1) | L1BM を 0/64 に置く版 |
| `cand4.vsm` | 22 | 22 (j=21, m=1) | L1BM を 320/384 に置く版 |
| `cand5.vsm` | 23 | 23 (j=21, m=2) | `mvrffadd/n64` を 2 語使う保険版 |

すべて `python3 problems/run_problem.py 46.matmul-tra-pkg-lmdram-16-256-16 --solution <cand>` で
`ACCEPTED!! score=22`（cand5 は 23）を確認済み。

## 短縮の要点

1. **MV を減らすには 16 長語単位の並べ替えが要る**
   - `mvrffadd/n<size> $lc $d`（L2BM→DRAM グループ間縮約）は、縮約した 64 長語を
     16 長語ずつ 4 group の DRAM に配る。1 命令で 32 長語/group を書くには
     `n128` とし、L2BM の 2 ブロックを
     `[g0 の 2 行, g1 の 2 行, g2 の 2 行, g3 の 2 行]` に並べておく。
   - 現行解は `mvrffadd/n256` + `mvp` 4 語で PDM 経由にしていた（MV 5 語）。
2. **l1bmm のフラット指定で行を自由に並べ替える**
   - `l1bmm@m $ll<[a0,a1,a2,a3]> $llb<b>` の `[ ]` はサイクルごとの読み出しアドレス（語単位）。
     これで 1 命令の 4 サイクルに MAB m の任意の 2 行組を入れて 32 長語を書ける。
   - group g の 4 行は GRF0 の 8 長語（行 r = LW 2r, 2r+1）。MAB0 が行 0–7、MAB1 が行 8–15。
3. **ハザードの実測**
   - PE→L1BM の後に同じ 16 長語ブロックを L1BM→L2BM で読むには 12 サイクル必要
     （10 では足りない。`nop` 相当で 3 ステップ空ける）。
   - GRF0 は 16 長語ブロック単位で 2 ステップ空けないと読めない。
     そのため最初の l1bmm はブロック 0 だけを読む形にし、2 行分は後続命令で上書きする。
   - L1BM→L2BM の直後に L2BM を読む MV を出すには 1 ステップ（`nop/1`）必要。
4. **nop を 1 行削る工夫**
   - 2 本目の l2bmr の読み出し窓の最後のブロックだけを、より早い行の命令で書く
     （`l1bmm@1 $llr[0,4,8,12] $llb144` で 160 の窓を先に書き、176 は後から
     `$llr[24,28,0,4] $llb176` で書く）。これで l2bmr を 3 ステップ後に置ける。

## ツール

- `check.py <cand>`: assemble3 + gpfn3_package_main を直接叩き、DRAM 期待値と比較（約 0.5 秒）。
- `dbg.py <cand> [extra.vsm]`: 任意の `d get` を足して L1BM/L2BM/GRF の中身を確認する。
