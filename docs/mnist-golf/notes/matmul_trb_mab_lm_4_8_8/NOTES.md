# matmul_trb_mab_lm_4_8_8 — 3 行化の検討結果（失敗）

現行 `problems/32.matmul-trb-mab-lm-4-8-8/answer.vsm` は公式 judge で
`ACCEPTED!! score=4 j=4 m=0`（2026-10-19 に再確認）。

3 行（score=3）を目指して 13 候補を検証したが、ACCEPTED は得られなかった。
以下は「なぜ 3 行が不可能か」を assemble3 / emulator / SDM で確認した制約から導いた結論。

## 1. 現行 4 行の構造

```
gbfn $lm8v $nowrite
gbfn $lm16v $nowrite; gmwrite $aluf $ly0
gbfn $lm0v $nowrite; gmwrite $aluf $ly4
gmmul $ly $aluf $ln0v
```

- 命令数 6（`gbfn` 3 + `gmwrite` 2 + `gmmul` 1）、ステップ数 4。
- score は flat モードの `j` 行数（= ステップ数）なので 4。
- `gbfn` の結果（`$aluf`）は**直後のステップでしか読めない**（SDM 3.6.1.16）。
  `nop`/ALU 無しのステップを挟むと `IALU is disabled` で落ちる（実測: g2.vsm）。

## 2. 3 行に必要な条件

- C の 32 値は 1 個の `gmmul` でしか作れない（vector 演算は 8 lane の elementwise で、
  8 項の縮約ができない。`imm` は 1 命令 1 定数で 32 値の直書きは 4 命令以上必要）。
- `gmmul` の行列は 8 行 8 列の BF 疑似単精度。`gmwrite` は 1 命令 4 行しか書けないので
  **最低 2 個の gmwrite** が必要。1 個の `hmwrite` で 8 行書けるのは half 経路のみ。
- `gmwrite` と `gmmul` は同じ行列レジスタ面 (`$x` / `$y`) を同時に使えない
  （`conflict readh mau`、実測: f2.vsm / p_a1.vsm）。
- 1 ステップに ALU は 1 個、`gmwrite` は 1 個まで。

したがって 3 ステップの形は
`s1: ALU+mwrite, s2: ALU+mwrite, s3: gmmul+ALU`
に限られる（mwrite 2 個と gmmul は別ステップ、各ステップに ALU 1 個）。

## 3. 不可能性の核心（LM0 同時読み出し制約）

同じステップで 2 命令が LM0 を読む場合、**全サイクルで同一アドレス**でなければならない
（SDM 3.6.4。実測: cand2.vsm 「Instruction field conflict between lm0 and in_lm0」）。
T 間接 (`$lmt...`) を使っても assemble3 は同じエラーで拒否する（cand13.vsm）。

- s1 の mwrite のソースは、直前 ALU が無いので**生の LM0 データ**しかない。
- B の 8 行のうち生データが有効 BF になるのは行 4–7 のみ。
  行 3 (`[124..131]`) は指数 6 と 7 が混在するため、生のままでは
  `Invalid block float format ... Maybe BFn/BFe is lacking`（実測: f1.vsm）。
- s1 の mwrite が行 4–7 を生で読むと、同じ s1 の ALU は同一アドレスしか読めないので
  `gbfn` も行 4–7 を変換する。すると s2 の mwrite（s1 の `$aluf` を使用）が書くのは
  同じ行 4–7 になり、行列の両半分が同じ 4 行になる。
- 行 0–3 を BF 化して書くには、その `gbfn` を s1 に置く必要があるが、s1 の mwrite は
  行 4–7 を読むためアドレスが一致せず、LM0 読み出し競合で assemble3 が拒否する。
- s1 に mwrite を置かず s2 に 2 個目の mwrite を置くと、s3 の gmmul と同一面で
  競合するか、4 ステップ目が必要になる。

## 4. 実際に到達できた最良（cand11.vsm, 3 行）

```
gbfn $lm8v $nowrite
gbfn $lm0v $nowrite; gmwrite $aluf $ly0
gmwrite $lm16v $lx4; gmmul $ly $aluf $ln0v
```

- assemble3 通過、score=3、実行成功。
- 行列 `$ly` には B 行 0–3 だけが書かれ、行 4–7 は 0。
- 結果は **16 value(s) correct, but 16 value(s) mismatch**。
  PE0/PE1（C 列 0–3）は完全一致、PE2/PE3（C 列 4–7）が 0。
- B 行 4–7 は生のまま有効 BF なので `gmwrite $lm16v $lx4` で書けるが、この書き込みと
  `gmmul $ly` を同一ステップに置くことはできず（面競合）、s3 で別面 `$lx` に書いても
  gmmul は `$ly` しか読めない。

## 5. half 経路（hbfn/hmwrite/hmmul）の限界

- `hbfn/9 $llm8vr` は 1 命令で B 8 行分（16 float/PE）を変換できるが、
  出力は 1 サイクル 4 half/PE（= 行列 1 行分）だけで、2 長語の後半は 0。
- `hmwrite $aluf $llx0` は 8 行を書くが、有効データは偶数行 0,2,4,6 の 4 行のみ
  （実測 d getbh）。`hmwrite` にマスクは付けられない（`Trailing letter after location`）。
- `hmmul $lx $aluf $ln0v` は longword dst で C のレイアウトに一致する位置
  (PE p の word 0,1) に書けるが、行列の有効行が 0,2,4,6 にしかないため
  出力位置 0,2,4,6（= 列 0,2,4,6 の word 0）しか埋まらず、半分以上が 0。
- 実測 cand12: 0 value(s) correct, 32 mismatch。
- 16x16 行列を 2 回の hmwrite で埋めるには 2 hbfn + 2 hmwrite + hbfn(A) + hmmul の
  6 命令が必要で、依存関係から最低 4 ステップ。

## 6. 候補と結果（すべて `problems/run_problem.py` で検証）

| 候補 | 内容 | 結果 |
|---|---|---|
| cand1 | raw B 2 回 + raw A gmmul | RUNTIME BF error（A 行 0 が不正 BF） |
| cand2 | raw B1 + gbfn A と同一行 | ASM: lm0 読み出し競合 |
| cand3 | gbfn A → GRF、raw B、gmmul | RUNTIME BF error |
| cand4 | 3 行に gbfn+gmwrite+gmmul | ASM: conflict readh mau（同一面） |
| cand5 | 4 行版の x を `$ly` に | 0 correct / 32 mismatch |
| cand6 | gbfn B1 + raw B 混在 | RUNTIME BF error |
| cand7 | h 経路 3 行 | ASM: conflict readh mau |
| cand8 | gmfma 版 | 0 correct / 32 mismatch |
| cand9 | gbfn B1 + raw B2 | RUNTIME BF error |
| cand10 | h 経路 3 行 | ASM: conflict readh mau |
| **cand11** | **B0–3 を面 y、B4–7 を面 x に分離** | **16 correct / 16 mismatch（最良）** |
| cand12 | h 経路 3 行（mask 無し） | 0 correct / 32 mismatch |
| cand13 | T 間接で読み出し競合の回避を試行 | ASM: lm0 読み出し競合 |

## 7. 結論

- 3 行（score=3）で C の 32 値をすべて一致させる構成は、上記の
  (a) BF 変換の直後ステップ依存、(b) mwrite 4 行制約、(c) gmmul と mwrite の面競合、
  (d) 同一ステップの LM0 同一領域読み出し制約、の 4 つを同時に満たせず作れない。
- 最良の 3 行候補 cand11 でも 16/32 一致にとどまり、ACCEPTED にならない。
- したがって現行の 4 行（`answer.vsm`, score=4）がこの問題の下限。
