# GPU 命令カバレッジ

対象は `docs/mncore_llm` の SDM 3.6 にある PE 命令式。
CPU の `Sim` と GPU の `gpu_run_program` が同じ VSM を実行し、最終状態が一致することを基準にする。

## 現状

| 分類 | 対応 | 主な不足 |
| --- | --- | --- |
| ALU | Passa, Xor, Max, Min, Rsqrt, Bfn(G), Msr, Msl, Zero, Imm, Add, Sub, Inc, Dec, Not, Lnot, And, Or, Lsl, Lsr, Bsl, Bsr, Packbit, Relu0..3, Relu, Floor, Ftoi, 固定 Subpeid | `Lrelud`/`Lreluo`/`Ilrelud`、`Bfe`、16/64 bit の大半、unsigned、`ext/rnd`、flush |
| MAU | f32 の FMA/MUL/ADD/PASSA、D の行列 write/read | D/H のベクトル MAU、H の行列、`neg/ext/rnd` の一部、flush |
| 行列 | F/G/D の write/read、F/G の matrix MAU | H、D の matrix MAU、マスク付き読み書き、T ソース |
| L1BM | Pbcast, Mbcast, Mwrite, Distrib, Gather, 1 長語 16x1 ffadd | 2 長語、M4 系、全 RRN、`l1bmr4`、turnaround `$lbi`、`l1bmm@` の 2 長語 |
| L2BM | Bcast, Bcast2, Distrib, Gather, FromL1b, Imcast, Reduce/Reduce2 全 RRN | `l2bmdars` / `l2bmdarw`（DAR） |
| MV | `mnist_train_step` の 168 文 | 文書上の全 variant の適合テスト、DAR 連携 |
| オペランド | 直接 Mem、Forward、固定 Subpeid、T | ベースアドレスレジスタ `$mb`/`$nb`、`j`、全 FixedKind、複数出力、`ext/rnd`、flush、行列マスク |
| 制御 | nop, mask, noforward/wait の一部 | `wait` の MV 待機意味論、並列発行条件の完全な検証 |

## テスト

- 既存: `gpu_run_program` が `mnist_train_step` を CPU と比較。
- 追加予定: 命令ごとに最小 VSM を生成し、CPU/GPU の全状態を比較する `gpu_conformance`。

## 進め方

1. ALU の全 opcode・精度・unsigned・`ext/rnd`・flush。
2. MAU の D/H、matrix MAU D/H、マスク。
3. L1BM の 2 長語・M4・全 RRN・`$lbi`。
4. L2BM の DAR。
5. オペランド形（ベース、`j`、複数出力）と `wait`。
6. `gpu_conformance` を全命令に広げ、`cargo test` に組み込む。
