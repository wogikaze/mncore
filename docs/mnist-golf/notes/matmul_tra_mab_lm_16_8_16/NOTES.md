# matmul_tra_mab_lm_16_8_16 — 14 行化の試行メモ

現行 `problems/44.matmul-tra-mab-lm-16-8-16/answer.vsm` は公式 judge で
`ACCEPTED!! score=15 j=15 m=0`。これを 14 行以下にできなかった記録。

## 現行 15 行の構造（実測で確認）

- T = 2 × MABID（`ipackbit $mabid $lm32v4 $t`、B の符号ビットは 0 なので実質 2 倍）。
  LM0 の A/B は MAB 内で共通だが、T で even MAB は A 左半（列 0–7）、
  odd MAB は A 右半（列 8–15）を読む。judge が見るのは MAB 0 のみ。
- 1–2 行目: B 左半 8 行を x 行列へ（`$lm32v4` / `$lm48v4` は adri=4）。
- 3–4 行目: y に A（T 経由）、同時に x（B）の列を `gmread`。
- 4–5 行目: `gbfn $mreadf` → GRF0 に B 転置（＝Bᵀ の 4 行分）。
- 5–6 行目: x に B 右半、7–8 行目に y へ Bᵀ左半を書き戻し、8 行目までに x へ Bᵀ右半を `$aluf` 直結で書く。
- 9–12 行目: `gmmul $ly/$lx` を 4 回。MAB 0 が C 行 0–7、MAB 1 が C 行 8–15。
- 13–15 行目: MAB 1 の GRF0（行 8–15、32 語）を 16 語×2 の 2 長語
  `l1bmm@1 … $llbi` で L1BM に送り、折り返しレジスタ `$llbi` から
  `l1bmm $llbi $lln32v` / `$lln48v` で全 MAB の LM1 へ放送。

## 14 行に必要な条件（逆算）

最後の放送読み出しを 14 行目に置くには、2 チャンクの GRF データが 10/11 行目に
揃っている必要がある（GRF 書き→読みは 1 ステップ空け、PE→L1BM 書きは GRF の
2 ステップ後、折り返し読みはその次）。すなわち 4 個の gmmul が 11 行目までに
終わり、s0v4 側の 2 個（Bᵀ左右）は 10 行目までに終わる必要がある。
Bᵀ は 1 ステップ 1 行列書き込みなので 2 枚目は 9–10 行目が最短 → 11 行目。

## 試した 14 行候補と拒否理由（すべて assemble3 が拒否）

1. `cand1.vsm`: 13 行目の `l1bmm@1 $llr0v $llbi` を 12 行目（最後の gmmul と同ステップ）へ。
   → `DataRaceError: A racy memory read at GRF0 address 0`（GRF は書き後 1 ステップ空けが必要）。
2. `cand2.vsm`: 同上で行 12–15 を GRF1 側へ逃がす。
   → 同じく GRF0 の DataRace（g11 が 11 行目に GRF0 を書くため）。
3. `cand3.vsm`: `l1bmm@1 $mauf $lbi` を各 gmmul の直後に置き、8 語チャンクを 4 本折り返す。
   → `Instruction field conflict detected between 'out_lm1' and 'out_lm1'`
   （1 ステップに LM1 書き込みは 1 命令だけ。gmmul と放送読み出しが 11/12 行目で衝突）。

## 実測で確認した他の制約

- `gmmul … $lln0v4`（2 長語 dst）は第 2 長語が 0 埋め（probe で確認）。MAU 出力は
  1 ステップ 2 語までなので、gmmul で 16 語書くことはできない。
- `hmwrite/<ll>` は 2 行/サイクル書けるが、F/G の行列は物理行 0,2,4,… を使うため
  H の物理行 0..7 と一致しない（`mat_shape` が F/G=(8,2), H=(16,1)）。
- L1BM 転送（`l1bmm@` / `l1bmm` / `l1bmd`）は PE の対応を入れ替えられない
  （読み出しは `l1bm[src+p]`, `l1bm[src+4+p]` 固定、`l1bmd` の mabdiff は MAB 間のみ）。
- 折り返し読みの語長は直前の折り返し書き込みと一致必須（`$lbi` と `$llbi` の取り違えで
  `Mismatch of word length in L1BM turnaround`）。
- LM1 は書き後 2 ステップ空けないと読めないので、gmmul の LM1 dst を放送元にはできない。

## 結論

上記の依存鎖（10 行列書き込み → 2 枚目の Bᵀ が 9–10 行目 → 最後の gmmul が 12 行目
→ GRF 2 ステップ + 折り返し 1 ステップ）で 15 行が下限。14 行は見つからず。
