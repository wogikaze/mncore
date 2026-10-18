# 04 — prologue RE (L1-16) と線消去の網羅確認（2026-10-18）

## 網羅確認: 静的フィルタ付き線消去は 0/520

`fastopt2.py --rounds 2 --workers 11` を main.vsm (93行) に対し実行:

```
baseline Result(ok=True, score=93, ...)
round 0 phase 1: no win (gen=408 asm=69 sim=339)   # 1命令移設→空行削除、静的条件を満たす全候補
round 0 phase 2: no win (gen=112 asm=112 sim=0)    # 空行化 DFS
no phase produced a win; stopping
DONE score=93 t=29s
```

- 併せて `fastopt.py`（静的フィルタ無しの単一命令移設 1995 候補）も 0 win 済み。
- **結論: 行の再配置による短縮はこの近傍では枯渇**（従来の結論を高速 sim で再確認）。
- 93→53 には「命令そのものを削る」段階的書き換えが必要。

## プロローグ L1-16 の RE 結果（確定）

境界（L16 終了直後）で本体 L17.. が消費する状態は次の **5 つだけ**:

| 対象 | 値（全 4096 PE で検証） | 供給元 |
|---|---|---|
| `$r0` (GRF0 w0) | `8b << 32`（MSB 半 32bit = b<<3; b=ブロック番号） | L13 |
| `$s0` (GRF1 w0) | `(8b<<32) \| ((mab>>1)<<10) \| ((l1b&1)<<4)` | L13/MSB, L6+L9/下位 |
| `$s28` (GRF1 w28) | `8 << 32` | L15 imm |
| `$t` | `0x4B000000` | L14 imm |
| `aluf` | `[0x4B000001..0x4B000004]`（= T \| [1,2,3,4]） | L16 = `ior $lr2v $t`、r2v = r2,4,6,8 = 1,2,3,4 |

- `$s0` の同定は全 4096 PE ダンプ（native sim 1 回, 0.1s）で `GREG1 addr0` を取得し、
  `bit4 == (l1bid&1)` を 4096/4096 確認、`lo == ((mab&14)<<9) | ((l1bid&1)<<4)` を確認。
- `$r0` は全 PE で `8*block`（既知の式と一致）。
- それ以外の L1-16 の書き込み（r2..r16, s31=599, omr15 等）は本体で不参照（dead）。

### 本体側の消費者

- `$r0` → L25 `iadd $r0 $s28v $n1/$imr1`（$n1 = 8b+8 相当）
- `$s0` → L24 `isub $s0 $r24v $omr1`（マスク生成。$r24v={32,408,4672} 系と比較）
- `$t` → L17 ほか多数（2^23 フロートトリック）
- `aluf` → L17 `fvadd $aluf -$t $lr102v $ls102v $ln102v` → 定数 1.0..4.0 を 3 メモリへ同時書き

### 定数 1..7 の生成機構（iinc の癖）

- `iinc $mreadf $lr2v4` は「10 進 1..7 を GRF0 addr 2,4,..,14 の長語に書く」（native sim と公式エミュで一致）。
- 同型で src を `$n1` にすると addr 2,6,10,14 に 1 が 4 個だけ（挙動が変わる）。
  → mread フォワーディング待ちを跨ぐ特殊挙動。プロローグで r2..r14 = 1..7 が必要な理由。
- 必要最小の dance: `dmwrite <x> $lx0; dmread $lx0 $lr0v4; iinc $mreadf $lr2v4`（x は T で代用可、値は不問）。

## 置換プロローグの設計（次セッションの出発点）

本体必要条件は上表 5 点。最小構成の方針:

1. **Pe A**: r2v=[1,2,3,4] を dance 3 行（`dmwrite $t $lx0` で 1 行節約可能か要検証→ probe.py）
2. **Pe B**: `$t`, `$s28` は imm 2 行（現行どおり）
3. **Pe C**: `$r0`/`$s0` を座標ビットから直接構築。必要なピース（シフト量）:
   - g1g0c → <<7（r14=7 を利用）→ bit 9,8,7
   - h2h1 → <<9（``9`` の定数が必要）
   - h0 → <<6（r12=6）
   - m3m2m1 → <<11（``11`` の定数が必要）
   - m0,p1p0 → <<3（r6=3）
   4 cycle のレーンを並列スロットとして使う（元実装 L5-13 と同じ機構、`$r[a,b,c,d]` の
   per-cycle フラット読みでシフト量を cycle 毎に変える）。
4. **別解**: `mncompile/generate.py` の `bitlinear_value` / `bitgather_value` / `_times` が
   まさにこの種のビット線形構築のコード生成器。係数ベクトル（c0, c_half, bits[12]）を
   与えれば最短風の VOp 列を生成できる。VProgram から VSM 断片を取り出して接続する道。

検証ループ（高速）:
- 境界一致: `trace.py --after 16,17`（公式, ~6s）で r0/s0/T/s28 を比較
- 意味: `python3 fastsim.py <candidate>`（native sim, 0.4s）→ ok
- 最終: `judge/judge-py/judge.py ... testcase.vsm <candidate>`（~1.2s）

## 参考: mncompile 資産

- `mncompile/sim.py` … native sim ラッパ（0.1-0.4s/run, 4096/4096 忠実）
- `mncompile/generate.py` … 座標ビット線形のコード生成（上記）
- `mncompile/schedule.py` … fwd/ハザード込みスケジューラ
- `mncompile/fmtseq.py` … FizzBuzz 型定数列の解析（コンパイラの 103 行解の戦略）
- `mncompile/benchmarks/results/20.fizzbuzz/report.json` … コンパイラ解 103 行
  （lower bound 77, scheduling gap 26, unit: alu 60 / mau 77）
