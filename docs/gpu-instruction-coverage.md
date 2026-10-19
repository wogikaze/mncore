# GPU 命令カバレッジ

対象は `docs/mncore_llm` の SDM 3.6 にある PE 命令式。
CPU の `Sim` と GPU の `gpu_run_program` が同じ VSM を実行し、最終状態が一致することを基準にする。

## 現状

| 分類 | 対応 | 主な不足 |
| --- | --- | --- |
| ALU | 全 32 opcode（zero/imm を除く ALU_OPS と `zero`/`imm`）。`d/f/g/h/l/i/s`、unsigned、入力 `r`/`e`、zero-flush、複数出力、OMR/T 出力、`msl`/`msr`、`bfe`/`bfn` 全精度・`hbfn/<n>`/`hbfe/<n>`、`lrelud`/`lreluo`/`ilrelud` | `$mb`/`$nb` 出力、`j`・T 間接アドレス、`$lbf` 入力、9 個以上の出力、`hbfn/<n>` の n が 6..9 外。ALU の `e` は CPU と同じく no-op（SDM 3.6.12 は `r` のみ定義） |
| MAU | f32 の FMA/MUL/ADD/PASSA、D の行列 write/read | D/H のベクトル MAU、H の行列、`neg/ext/rnd` の一部、flush |
| 行列 | F/G/D の write/read、F/G の matrix MAU | H、D の matrix MAU、マスク付き読み書き、T ソース |
| L1BM | SDM 3.6.8 の全形式: 1/2 長語、M4、全 24 RRN、`ext`/`round`、`$lbi`、Gather/Distrib、マスク/flush（`gpu_l1_conformance`） | `$lbf`、L1BM 書き込みの forwarding ソース、BAR/T 間接/`j`、`$lbi` の未定義読み出しエラー |
| L2BM | Bcast, Bcast2, Distrib, Gather, FromL1b, Imcast, Reduce/Reduce2 全 RRN | `l2bmdars` / `l2bmdarw`（DAR） |
| MV | `mnist_train_step` の 168 文 | 文書上の全 variant の適合テスト、DAR 連携 |
| オペランド | ALU: 直接 Mem、Forward（`aluf`/`mauf`/`mreadf`）、固定値 6 種、T、WL 1/2/4、複数出力、`r`/`e`、zero-flush、単一行マスク・`mask` ディレクティブ | ベースアドレスレジスタ `$mb`/`$nb`、`j`・T 間接、`$lbf`、`hbfn` の範囲外 `<n>`、行列マスク |
| 制御 | nop, mask, noforward/wait の一部 | `wait` の MV 待機意味論、並列発行条件の完全な検証 |

## テスト

- `gpu_run_program` が `mnist_train_step`（PE 行 2,635）を CPU と比較し、全状態一致。
- `gpu_alu_conformance` が ALU の全 opcode・精度・unsigned・`r`/`e`・flush・複数出力を網羅する
  VSM を生成する。現在 142 config / 524 PE 行。各行の `aluf`・OMR・T と、最終的な
  4 メモリ全体を比較する。
  ```sh
  cd viz/core
  cargo run --release --bin gpu_alu_conformance
  ```
- 既存の `gpu_vsm_alu`、`gpu_vsm_mask`、`gpu_vsm_gbfn`、`gpu_vsm_matrix` も引き続き 0 mismatch。

## 進め方

1. ✅ ALU の全 opcode・精度・unsigned・`r`/`e`・flush・複数出力（`gpu_alu_conformance`）。
2. MAU の D/H、matrix MAU D/H、マスク。
3. L1BM の 2 長語・M4・全 RRN・`$lbi`。
4. L2BM の DAR。
5. オペランド形（ベース、`j`、複数出力）と `wait`。
6. `gpu_conformance` を全命令に広げ、`cargo test` に組み込む。
