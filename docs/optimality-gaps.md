# MN-Core 最適性: できていないこと

この文書は [README](../README.md) の「Lean optimality audit」と
[proofs_lean/README.md](../proofs_lean/README.md) からリンクされる、未完了部分の一覧である。
2026-10-22、コミット `d347038`（証明開発）と `db3f589`（状況・監査）時点。

## 1. 完成しているもの（1/73）

| 問題 | Accepted | Lean の上限 | Lean の下限 | 定理 |
| --- | ---: | --- | --- | --- |
| `1.plus-one` | 2 | 2行・無条件 | 2・無条件 | `welcomePublicMachine_optimal`（hazard-aware whole machine、公開仕様）。全PE版 `welcomePublicAllPEs_optimal`、非有界版 `welcomePublicUnbounded_optimal`、両方の `welcomePublicBoundedAllPEs_optimal` も証明済み。 |

`1.plus-one` 以外で、Accepted 語数と Lean 下限が一致している問題はない。

## 2. 部分証明（上限と下限が揃っていない）

| 問題 | Accepted | 上限（正しさ） | 下限（到達点） | 残っている前提 |
| --- | ---: | --- | --- | --- |
| `12.convert-endian` | 3 | `cendAnswerCorrect`（sealed whole-machine、無条件） | `cendLowerBound_three_of_narrowedResiduals`（3、条件付き） | `CendBlockFloatLinesRefuted` / `CendMatrixMAULinesRefuted` / `CendMatrixFamiliesResidual` / `CendTwoLineCommitShape` |
| `3.relu` | 2 | sealed 仕様・両行の値 readback・全4096 PE walk・line-level step まで | 未着手 | 2行 `Correct`、`LowerBound 2`（`.double` low raw、2式 issue 拒否、`.word`/`.long` 8語不足、nop/mv/empty、非 relu 式は負入力 witness）。line 0 の step 証明は `ReluLine0.lean` にあるが build が OOM（exit 137）で未追跡。 |
| `4.relu-grad` | 3 | 仕様・score・2行 gap 証明 | `reluGradLowerBound_three_of_residual`（3、条件付き） | `ReluGradLineExecResidual` の `answer`（relu link）/ `oneLine` / `twoLine` |
| `2.fmul7` | 6 | 仕様・5行解・score・形状被覆・imm 行 executor・bar1 修正版 shape bound | `fmul7_shape_score_five_zeroBar`（5、条件付き） | `Fmul7AnswerExecutorLink`（fvmul 4行 + values）、`Fmul7LineShapeResidualZeroBar`、`Fmul7GeneralResidual`（非形状行の一般反駁） |
| `1.a-b` | 3 | なし | `abLowerBound_two_of_residuals`（2、条件付き） | `ABPlainDoubleResidual` / `ABNonPlainResidual`。目標は3で、下限2からの引き上げが別途必要。 |
| `3.a-plus-b` | 6 | なし | `aplusbLowerBound_two_of_residual`（2、条件付き） | `AplusBPEUnrefuted`。目標6。 |
| `2.plus-two` | 5（公式AC）/ 6（普遍） | 6語解は探索のみ | `plusTwo_lowerBound_two`（2、`DischargedALULine` クラス限定） | 公式ACの5語は Lean で普遍的に誤りと証明済み。目標は6で、入力依存的値来歴が必要。 |
| `4.mul7` | 6 | なし | `mul7LowerBound_two_of_peFootprint`（2、条件付き） | `Mul7PELineFootprint`。目標6。 |

## 3. 全問題に効く未完了

- **全ISAの網羅**: `proofs_lean/coverage.json` は `isa_exhaustiveness_proven: false`,
  `full_semantics_implemented: false` のまま。モデルが実行できない命令は
  `step = none` になり、下限のプログラム空間から除外される。実機では正しいかもしれない
  プログラムを落とす方向なので、下限の実機移行には全ISA意味論の完成が要る。
- **parser / assembler 対応**: `proofs_lean/ISSUE_AUDIT.md` の通り、VSM source から
  `InstructionLine` への全域対応、`l2bmdars` の同時発行例外、完全な合法性は未証明。
- **sealed machine と whole machine の差**: `cendAnswerCorrect` と relu/fmul7 の上限は
  `executeNormalizedLine`（hazard 層なし）の上にある。公開問題の hazard-aware
  `Correct` への lift は Welcome 以外で未完了。relu の lift は
  `WelcomeWholeMachineOptimal.lean`（935行）のパターンで ~1–2k行と見積もっている。
- **静的アセンブラ検査**: `assemble3` の `DataRaceError` などのテキスト検査はモデルに
  入っていない。下限には保守的（広い空間で示すほど強い）だが、上限の受理証明には別途必要。
- **未追跡の WIP**: `ReluLine0.lean`（line 0 step 証明、build が OOM）と
  `ReluCtxFrame.lean`（`ReluOpt.lean` と `peContext` frame が重複）はコミットしていない。

## 4. 信頼境界

- 証明開発は `sorry` / `admit` / `axiom` 宣言 / `native_decide` を含まない。
- 主要定理の `#print axioms` は `propext`, `Classical.choice`, `Quot.sound` のみ。
- 旧 `ConvertEndian.answerDatapath_is_byteSwap` は `bv_decide` の native axiom を含むが、
  新しい cend 連鎖は `ByteSwapKernel` 経由でこれを避けている。
- `lake build ProofsLean` は 967 jobs で成功（`ReluLine0` / `ReluCtxFrame` は root 未 import）。

## 5. 未着手

- challenge 後半（13–25）と MNIST 48問のうち、形式的仕様・下限とも未着手のもの。
- `16.count-up` / `19.inversion` / `20.fizzbuzz` などの L2/MV/DRAM 系。
- FizzBuzz 52語トラックの Lean 化（`research/FINAL-STATUS.md` の予備解析は CP-SAT と
  全列挙によるもので、Lean 証明ではない）。
