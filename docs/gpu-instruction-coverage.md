# GPU 命令カバレッジ

対象は `docs/mncore_llm` の SDM 3.6 にある PE 命令式。
CPU の `Sim` と GPU の `gpu_run_program` が同じ VSM を実行し、最終状態が一致することを基準にする。

## 現状

| 分類 | 対応 | 主な不足 |
| --- | --- | --- |
| ALU | 全 32 opcode（zero/imm を含む）。`d/f/g/h/l/i/s`、unsigned、入力 `r`/`e`、zero-flush、複数出力（8 個まで）、OMR/T/BAR 出力、`msl`/`msr`、`bfe`/`bfn` 全精度・`hbfn/<n>`/`hbfe/<n>`、`lrelud`/`lreluo`/`ilrelud`。入力の `$mb`/`$nb` 加算・T 間接・`j` も全カーネルで対応 | `$lbf`・forwarding の全ソース（ALU/MAU/行列/L1BM 書き込み）、最大 16 出力（`issue::check` により同一メモリ種別への複数出力は不可）、`hbfn/<n>` の n が 6..9 外。ALU の `e` は CPU と同じく no-op（SDM 3.6.12 は `r` のみ定義） |
| MAU | ベクトル MAU D/F/G/H の fma/mul/add/passa（u/d/round、neg/e/r、wl 1/2/4、LM/GRF/T/forwarding、nowrite、マスク/flush、T/OMR/複数出力）。matrix MAU D/F/G/H（mwrite/mread 含む）。`gpu_mau_conformance` 133 設定・7,640 行 | 不正 block-float 入力のエラー再現、matrix write のマスク（SDM に無い） |
| 行列 | D/F/G/H の write/read、matrix MAU、row wrap、neg/e/r、nowrite、複数 PE 出力、マスク/flush、T/OMR/BAR | 不正 block-float 入力のエラー、matrix MAU BAR 出力の conformance（乱数が BF 不正になりやすい） |
| L1BM | 全形式（1/2 長語、M4 系、全 RRN と `r`/`e`、`l1bmd` の分配・結合、`$lbi`、BAR/T/j、BAR 出力、`$lbf`/`$aluf`/`$mauf`/`$mreadf` ソース） | forwarding 無効時のエラー再現 |
| L2BM | 全形式（Bcast/Bcast2/Distrib/Gather/FromL1b/Reduce/Reduce2/Imcast、全 RRN、全 L1B 集合）と `l2bmdars`/`l2bmdarw`（DAR/DARBUF） | なし |
| MV | 全 25 基本モード（mvnop、mvp の全組み合わせと並列形、mvb/mvb2/mvb4、mvd の 4 方向、mvr/mvr2/mvr4 の全 RRN）、DRAM 間接参照（`$di`、`nd`、送受信両方の間接） | DRAM 間接参照の `nd` 省略時の公式エミュレータとの差（下記） |
| オペランド | ALU/MAU/L1BM/行列の直接 Mem、Forward（`aluf`/`mauf`/`mreadf`）、固定値 6 種、T、WL 1/2/4、複数出力、`r`/`e`、zero-flush、単一行マスク・`mask` ディレクティブ、`$mb`/`$nb` の読み書き、T 間接、`j`/madpe | `$lbf`、`hbfn` の範囲外 `<n>`、行列マスク、forwarding 無効時のエラー再現 |
| 制御 | nop、mask、noforward、wait、forwarding 有効/無効の追跡（無効な forward 読み出しは CPU と同じく実行前に失敗） | エラーメッセージ文言の一致 |

## テスト

- `gpu_run_program` が `mnist_train_step`（PE 行 2,635）を CPU と比較し、LM0/LM1/GRF0/GRF1、
  行列、OMR、T、`aluf`/`mauf`/`mreadf`、L1BM、L2BM、`$lbi`、BAR、PDM、DRAM、DAR の
  全状態が一致する。
- `gpu_mem_conformance` が L2BM・DAR・MV・オペランド・制御の各形式を生成し、CPU `Sim` と
  GPU の全メモリを比較する。現在 697 case。詳細は
  [gpu-backend.md](gpu-backend.md#メモリパスの適合テストgpu_mem_conformance)。
  ```sh
  cd viz/core
  cargo run --release --bin gpu_mem_conformance
  ```
- `gpu_l1_conformance` が L1BM の全形式を 7 section × 3 seed で比較する。
- `gpu_mau_conformance` が MAU と行列の 133 設定・7,640 行を生成し、`mauf`/`aluf`/`mreadf`、
  行列、OMR、T、4 メモリを比較する。
- `gpu_alu_conformance` が ALU の全 opcode・精度・unsigned・`r`/`e`・flush・複数出力を網羅する
  VSM を生成する。142 config / 524 PE 行。各行の `aluf`・OMR・T と、最終的な
  4 メモリ全体を比較する。
- 既存の `gpu_vsm_alu`、`gpu_vsm_mask`、`gpu_vsm_gbfn`、`gpu_vsm_matrix`、`gpu_vsm_mv`、
  `gpu_vsm_l2`、`gpu_vsm_l2red` も引き続き 0 mismatch。

## DRAM 間接参照のアドレス語

SDM 3.5.6 の本文はアドレス語の単位を「6 長語」と書くが、同じ節の例と公式エミュレータは
16 長語単位で計算する。CPU と GPU は公式エミュレータに合わせて

```
chunk i (16 長語) の DRAM アドレス = 16 * (DAR[(M + i/N) % 1024] + i % N)
```

を使う（`nd` 省略時は `16 * DAR[(M + i) % 1024]`）。DAR のエントリ自体は 32 bit で、
L2BM の 1 長語が 2 アドレス語（MSB が偶数番地）になる。
この解釈は、DAR を使う `problems/challenge/16.count-up` を CPU `Sim` と公式エミュレータで
実行し、84,000 値が一致することで確認した。

公式エミュレータは `nd` を省略した `$di` を受け付けるが、その場合 DRAM アクセスを
行わない（観測）。SDM は「N は無限大」と定義しているため、本実装は SDM に従って
`DAR[M+i]` を使う。`nd0` は CPU と同じくエラーにする。

## 複数命令式の 1 ステップ実行

CPU は 1 ステップ内の全命令式の入力を読んでから書き込みを適用する。GPU は命令式ごとに
カーネルを順に起動する。アセンブラが受理する行では、同一グループの命令式は 1 つまで、
同一 PE メモリへの書き込みは 1 つまで、同一メモリの読み出しアドレスは全命令式で同一、
forwarding レジスタを更新する命令式も各レジスタにつき 1 つだけなので、順次実行しても
最終状態は CPU と一致する（`gpu_mem_conformance` の複数命令式を含む制御 section で確認）。
アセンブラの並列発行条件を満たさない行は `issue::check` が拒否する。

## 進め方

1. ✅ ALU の全 opcode・精度・unsigned・`r`/`e`・flush・複数出力。
2. ✅ L1BM の全形式。
3. ✅ L2BM の DAR を含む全形式。
4. ✅ MV の全基本モードと DRAM 間接参照。
5. ✅ オペランド形（`$mb`/`$nb`、`j`、T 間接、固定値）と noforward/wait。
6. MAU の D/H、matrix MAU D/H、行列マスク、`$lbf`。

## 最終検証（2026-10-20）

| 項目 | 結果 |
| --- | --- |
| `gpu_alu_conformance` | 142 設定 / 524 行 0 mismatch |
| `gpu_l1_conformance` | 1,329 ケース × 3 seed 0 mismatch |
| `gpu_mau_conformance` | 133 設定 / 7,640 行 0 mismatch |
| `gpu_mem_conformance` | 697 ケース 0 mismatch |
| `gpu_run_program mnist_train_step` | 1,572 PE 行 0 mismatch（lbf/forwarding 比較込み） |
| `difftest_prog` 全 73 問題 + 全 challenge 解 | 0 mismatch |
| `cargo test --release` | 28 件通過 |

全問題の比較は `viz/core/scripts/check-conformance.sh`（`--gpu` で GPU 側も）と
`tests/problem_conformance.rs` で回帰ガードにした。詳細は
[gpu-backend.md](gpu-backend.md) の「検証の一本化」を参照。

命令形式の不足は解消した。残る差は実行時エラーの再現（不正 block-float、forwarding 無効の文言）と、
DRAM 間接参照で `nd` 省略時に公式エミュレータがアクセスしない点だけ。
