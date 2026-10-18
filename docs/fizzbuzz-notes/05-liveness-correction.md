# 05 — 2026-10-18 再開セッション: 前提の修正と次の一手

## 確定した訂正（重要）

04 の「本体が必要とするプロローグ状態は 5 つだけ（r0, s0, s28, t, aluf）」
「r2..r16, s31 は dead」は **誤り**。

`main.vsm` から次を個別に外すと score は 93 のままだが出力が壊れる（fastsim）:

| 除去した命令 | 結果 |
|---|---|
| `imm i"56" $r16/1000` (L2) | mism=3576 / 4096 |
| `imm i"599" $s31` (L3) | mism=3512 / 4096 |
| 両方 | mism=3576 |

理由: L39 `iadd/$imr15 $s5 $r[6,10,16,71] $s129v2` が **r16 を読む**。
s31 も本文のどこかで読まれる（`$s31` の直接 grep では出ないため、複合オペランド経由）。
→ プロローグ置換の設計は「境界 5 値」ではなく、**本文の全 liveness を取り直してから**やり直す。

## 検証ツールの注意

- `assemble3` の hazard checker を通っても、`$aluf` など **フォワーディングの「直前ステップ」意味**が
  変わるマージは受理されることがある（例: `imm ui"0x4b000000" $t; fvadd $aluf ...` は asm OK・judge NG）。
- したがって行マージの受理判定は必ず `fastsim.check(text, verify=True)` まで通す。
  `pack2.py` を追加（asm → fastsim の二段判定）。

## 現在地

- baseline: `main.vsm` = 93 行 = ALU 66 + 非 ALU 27（nop 8 / MV 2 を含む）。
- 53 行の必要条件: **ALU ≤ 51**（ALU は 1 行 1 命令、MV 2 行は固定）。
- 行再配置・単命令移設の近傍は prior run で枯渇（fastopt/fastopt2 0 win、今回も再確認）。

## 次の一手（優先順）

1. **canvas を 2 長語で持つ**: L78–L84 の pack 6 ALU を削る。
   現在 canvas は LM0 の 4 ワード（`$mt[0,4]`…`$mt[3,7]`）に分かれて書かれ、後段で
   8bit ずつ詰めている。L50/L57–L76 の書き込み先を「隣接する 2 長語」に変えれば
   `l1bmd $lm0 $lb0` 系 1–2 命令で置換できる可能性。
2. **プロローグ再設計**: ただし liveness を取り直す（上記訂正）。
   `trace.py` で L16 直後の全 GRF/LM を dump し、本文が読む集合を機械的に列挙する。
3. **float 定数の MAU 生成**: imm 20 本のうち float 系（63, 1/63, 1/71, 1/79, 0.1, 0.01, 0.001,
   0x4b0000xx）を MAU 演算に移し、ALU 行を削る。MAU は 1 行 2 グループまで同居可。
   現在 MAU 43 命令 / 27 行なので、ALU 行へ載せ替える余地はある。

## 検証ループ

```
cd .worktrees/fizzbuzz-shorten
python3 .recursive/run/fizzbuzz-shorten/fastsim.py <cand>     # 0.4s
python3 problems/run_problem.py challenge/20.fizzbuzz --solution <cand>  # 1.2s
```

## 追記（round 2）

- `imm i"8" $r8` (L78) は二役: (a) r8 に 8（L81/L83 のシフト量）、(b) `$aluf` = 8 を L79 の
  `ilsl $mt[0,4,0,4] $aluf` に渡す、(c) L77 `lpassa ... $t` → L79 `$mt...` の **T レースの 1 ステップ埋め**。
- L78 を削除し L79 を `$s28`、L81/L83 を `$r16` に置換すると:
  - `fastsim` は **ok, score=92, mism=0** を返す（native sim はハザードを見ない）
  - `assemble3` は `DataRaceError: racy memory read at T ... at line 78` で拒否。
  → **fastsim 単独では不十分。assemble3（hazard checker）→ fastsim → judge の順で判定する。**
- canvas は LM0 ではなく **T レジスタ**（`$mt[...]`）上にある。L57–L76 の `$mt[...]` 書き込み先を
  「隣接 2 長語」に変える案は、T のアドレス体系（0–43）とマスク書き込みの理解が前提。
