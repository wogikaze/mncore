# Lean 基盤計画の進捗（Phase 0→4）

計画: `research/lean-plan.md` の Phase 0 → 4。目標は worklist 順（3-3 実機モデルでの Welcome 最適性）に到達すること。

## Phase 0 — 完了
- `proofs/lowerbound/` を `research/preliminary/fizzbuzz-delivery/` へ移動。
- README 冒頭に「**THIS IS NOT A LEAN PROOF**」バナーを追加（CP-SAT UNSAT は Lean の項ではない）。
- `proofs/README.md` に規約を明文化（`proofs/` は Lean カーネル検証済みのみ）。
- `research/FINAL-STATUS.md` / `state.json` / `lower-bounds.md` の「成果B達成」記述を撤回し「予備解析」に変更。
- 確認: `grep -rn "proofs/lowerbound" research proofs` → 0 件（logs 内を除く）。

## Phase 1 — 進行中（第1増分 完了）
新規 `proofs_lean/ProofsLean/WholeMachineMachine.lean`（`lake build` 成功、838 jobs）:

```lean
noncomputable def wholeMachine : ProofsLean.PartialMachine where
  Line := Issue.InstructionLine
  State := HazardAwareState
  Input := Unit
  step := fun line state => executeHazardAwareNormalizedLine line.toNormalizedLine state
  legal := fun _ => True
  lineCost := Issue.InstructionLine.cost
  positiveCost := Issue.InstructionLine.cost_positive
```

証明済み:
- `wholeMachine_legal_all` — 広い legal（方針どおり）
- `wholeMachine_step` — step が hazard-aware 遷移と定義的に一致（rfl）
- `wholeMachine_rejects_issue_while_stalled` — 停止中の発行は `.failure`
- `wholeMachine_step_ok` — 成功は実行器に由来（frame 推論の入口）
- `wholeMachine_not_complete_of_unknown` — `.unknown` 行が残る限り `seal` 不可

`coverage.json`: `phase_3_state_footprint.whole_machine` を追加、`connected_to_machine_step: "partial"`。

### Phase 1 第2増分（完了）
- `wholeMachine_legal_iff_partialMachine_legal` — 両機の legal 領域が一致（`State := Unit` の placeholder と実状態機で合法性は同じ）
- `wholeMachine_normalizedExecutableLine_legal` — 正規化出力行が wholeMachine でも legal
- `lake build` 838 jobs 成功
- 注: マスクディレクティブ用の橋渡し定理は型が合わず撤回（推測で書いたものを削除）

### Phase 1 第3増分（完了）
- `wholeMachine_nop_step` — `wholeMachine.step` の最初の等式（正の count、wait なし）。
  既存の `executeHazardAwareNormalizedLine_positive_nop` を `simpa` で橋渡し。
  `lake build` 838 jobs 成功。
- `coverage.json` の `whole_machine.step_equations` に記録。

### Phase 1 の残作業
1. `partialMachine`（`State := Unit`）を `wholeMachine` に置換し、`normalizedExecutableLine_legal` の接続先を差し替える
2. issue 拒否 → `.failure` を `executeNormalizedLine` 経由でも示す（`integerProducerMachine_issue_failure` を経由）
3. ~~`.unknown` を返す行の列挙~~ **完了**（`coverage.json` の `whole_machine.unknown_sites`）:
   hazard-aware ラッパ2箇所、PE 行3箇所（wait pending / 入れ子実行器 / 非対応 producer の fallback）、
   nop の未完了タグ、非 nop MV。Welcome は `.pe` + iinc/zero/imm のみなので各所は不在か既存補題で落とせる見込み。
4. `python3 proofs_lean/scripts/check.py` を通す（クリーンビルド + sorry/axiom 検査）

## Phase 2–4 — 未着手


## check.py の現状（ラウンド5）

`python3 proofs_lean/scripts/check.py` は **既存の証拠の陳腐化**で停止する。今回の変更が原因ではない。

1. `ISA boundary experiment: viz/core/src/vsm.rs` — **修正済み**。`check_isa_parser_bounds.py --output proofs_lean/evidence/isa-bounds/reference.json` を再実行し、3410 probes を再記録した（`viz/core/src/mv.rs` も同時に更新）。
2. `answer encoding source: problems/34.matmul-trb-mab-lm-4-16-8/answer.vsm` — **未修正**。`check_answer_encoding_reference.py` の再実行が必要。73 問分のアセンブル出力を再取得する。
3. その後さらに別の証拠セットが陳腐化している可能性がある（未確認）。

`docs/formal-semantics-worklist.md` の 0-4 にも「2026-10-17 時点で GitHub Actions は失敗しており、check.py は judge 資産の欠落で停止」と記録されている。
**したがって当分の受け入れ基準は `lake build <変更モジュール>` とし、`check.py` を通すのは別タスク（証拠の再生成）として扱う。**


## check.py の停止点（ラウンド6で更新）

証拠を再生成して進めた結果、残る停止点は **catalog のハードコードされた期待値** になった。

1. ~~ISA boundary~~ → 再生成済み（3410 probes）。
2. ~~answer encoding の source hash~~ → `check_answer_encoding_reference.py` を再実行（73 answers / 1023 words）。
3. **`catalog.py:624`** — 期待値 `{"j": 984, "m": 57}`（計 1041）に対し、現コーパスは `{"j": 966, "m": 57}`（計 1023）。
   差は **j が 18 語少ない**。問題解答が短縮されたことを示す（リポジトリの履歴に短縮コミットがある）。
   → 定数を書き換えるのは**監査上の主張の変更**なので、勝手に更新せず保留。

### 判断が必要な点
`catalog.py` の期待値を現コーパス（966/57）に合わせるか、どの解答が 18 語短くなったかを特定して
意図的な変更だと確認してから更新するか。**Phase 0–4 の Lean 作業とは独立**なので、Lean 側は
`lake build` を基準に進め、check.py は別タスクとして切り離す。


## ラウンド7: `wholeMachine_rejects_issue` の試行と撤回

- 狙い: `checkParsedTopLine line.toParsed = false` なら `wholeMachine.step line state = .failure`
  （広い legal の方針で、issue 違反が `.unknown` ではなく既知の失敗になることを示す）。
- 実装: `executeHazardAwareNormalizedLineCore` は `Id.run do` の early-return 構造で、
  `simp [executeHazardAwareNormalizedLineCore, ...]` では未解決ゴールが残った
  （`WholeMachineMachine.lean:121:47 unsolved goals`）。
- 対処: **定理を撤回**し、モジュールを 838 jobs で green に戻した。壊れたビルドを残さない。
- 次に試すべきこと: `executeHazardAwareNormalizedLineCore` の `Id.run do` を展開する補題
  （`normalizedLineWaitTag?` / `line.toInstruction?` の具体的な簡約）を先に用意する。
  `Id.run do` の分岐は `split` + `simp_all` で落とす必要があり、現状の一括 `simp` では届かない。


## ラウンド8: core レベルの issue 失敗を証明（成功）

- `executeHazardAwareNormalizedLineCore_pe_issue_failure`:
  `checkParsedTopLine (InstructionLine.pe exprs).toParsed = false` なら
  `executeHazardAwareNormalizedLineCore (.pe exprs) state = .failure`。
  証明は `simp [executeHazardAwareNormalizedLineCore, NormalizedLine.toInstruction?, rejected]`。
- `lake build` 838 jobs 成功。
- ラッパー側（`executeHazardAwareNormalizedLine`）の同型定理は `Id.run do` の
  `let state ← match ...` の bind が残り simp で閉じなかったため**今回は見送り**（未解決ゴール）。
  次は `executeHazardAwareNormalizedLine_pe_eq_core`（notStalled と wait タグなしで core に落ちる）
  を先に示す。


## ラウンド9: ラッパー簡約補題は未完成（2方式とも失敗、撤回）

対象: `executeHazardAwareNormalizedLine (.pe exprs) state = executeHazardAwareNormalizedLineCore (.pe exprs) state`
（`notStalled` 仮定下）。

| 試行 | 内容 | 結果 |
|---|---|---|
| 1 | `simp [executeHazardAwareNormalizedLine, normalizedLineWaitTag?, notStalled]` | 未解決ゴール（128:66） |
| 2 | `unfold` → `simp only [notStalled, Option.isSome_none, ...]` → `simp [normalizedLineWaitTag?, Id.run]` | 同じ位置で未解決 |

原因の見立て: `let state ← match ... | none => pure state | some tag => ...` の
`Id` モナド bind が残る。`Id.run`/`Bind.bind` の簡約補題を明示的に用意しないと閉じない。
定理は撤回し、モジュールは 9 定理・838 jobs で green を維持。


## ラウンド10: ラッパー簡約を証明（成功）— 前回の定理は偽だった

**重要な訂正**: ラウンド9で失敗した定理は、仮定不足で**そもそも偽**だった。
`normalizedLineWaitTag?` は `.pe` に対して式を走査する
（`expressions.findSome? fun e => parsedExprWaitTag? e.toParsed`）ため、
wait タグが無いという仮定なしには `none` に簡約できない。

修正後の定理（証明成功、838 jobs）:
```lean
theorem executeHazardAwareNormalizedLine_pe_eq_core (exprs : List NormalizedExpr)
    (state : HazardAwareState) (notStalled : state.stalledPEIssue = none)
    (noWait : (exprs.findSome? fun e => parsedExprWaitTag? e.toParsed) = none) :
    executeHazardAwareNormalizedLine (.pe exprs) state
      = executeHazardAwareNormalizedLineCore (.pe exprs) state
```

これで core レベルの定理（issue 失敗など）を `wholeMachine.step` に持ち上げる道が開けた。
`wholeMachine_pe_issue_failure` は今回 simp が閉じず未完成（撤回）。


## ラウンド11: `wholeMachine_pe_issue_failure` 成功

`show` で `wholeMachine.step` を実行器に読み替え、`rw` でラッパー簡約補題を適用し、
`exact` で core レベルの定理を渡す構成で通った（838 jobs）。

```lean
theorem wholeMachine_pe_issue_failure (exprs) (state) (notStalled) (noWait) (rejected) :
    wholeMachine.step (.pe exprs) state = .failure
```

これで Phase 1 の「issue 違反は legal を狭めず step の失敗にする」が `wholeMachine` 上で証明された。
累計 11 定理。次は Phase 2（footprint frame）の着手、または `check.py` の証拠再生成の続き。


## ラウンド12: Phase 2 の最初の frame 補題（成功）

```lean
theorem wholeMachine_nop_frame (state : HazardAwareState) (count : Nat)
    (notStalled : state.stalledPEIssue = none) :
    ∃ next, wholeMachine.step (.nop ⟨count+1, _⟩ none) state = .ok next ∧
      next.machine.peRegisters = state.machine.peRegisters ∧
      next.machine.l1bm = state.machine.l1bm ∧
      next.machine.blockMemory = state.machine.blockMemory ∧
      next.machine.maskDirective = state.machine.maskDirective ∧
      next.machine.forwarding = state.machine.forwarding
```
`wholeMachine_nop_step` から直接従う。838 jobs 成功。

Phase 2 の一般形（全行について footint 外のフィールドが不変）の雛形になる。
次は `.pe` 行について同様の frame を、`executeIntegerProducerInstructionLine` の
成功形から導く。


## ラウンド13: MV 行のラッパー簡約（成功）

`normalizedLineWaitTag? (.mv _) = none` は定義上成り立つので、`.pe` と違い追加仮定は不要。

```lean
theorem executeHazardAwareNormalizedLine_mv_eq_core (transfer : NormalizedMv)
    (state : HazardAwareState) (notStalled : state.stalledPEIssue = none) :
    executeHazardAwareNormalizedLine (.mv transfer) state
      = executeHazardAwareNormalizedLineCore (.mv transfer) state
```

838 jobs 成功。これでラッパー簡約は `.pe`（noWait 必要）と `.mv`（不要）の両方をカバー。
残る `NormalizedLine` は `.nop` と `.maskDirective` だが、`.nop` は wait タグを持ちうるので
`.pe` と同型の仮定が要る。`wholeMachine` の `Line` は `InstructionLine` なので
mask directive は対象外（ProgramLegality 側で扱う）。


## ラウンド14: nop 行のラッパー簡約（成功）

```lean
theorem executeHazardAwareNormalizedLine_nop_eq_core (count : Nat)
    (state : HazardAwareState) (notStalled : state.stalledPEIssue = none) :
    executeHazardAwareNormalizedLine (.nop count none) state
      = executeHazardAwareNormalizedLineCore (.nop count none) state
```
`normalizedLineWaitTag? (.nop _ none) = none` が定義上成り立つので追加仮定は不要。838 jobs 成功。

これで `InstructionLine` が作りうる3種類（pe / nop / mv）すべてについてラッパー簡約が揃った。
残るは各ケースの step 等式と frame で、Phase 2 の一般形へ進める状態。


## ラウンド15: ライブラリ全体ビルドで統合を検証

`lake build ProofsLean` → **849 jobs, Build completed successfully**。
新モジュール `WholeMachineMachine` はルート `ProofsLean.lean` から import され、
全体ビルドに統合されていることを確認した（モジュール単体ビルド 838 jobs より強い検証）。

`check.py` は依然として catalog の期待値（966/57 vs 984/57）で停止するため、
現時点の受け入れ基準は「`lake build ProofsLean` が通る」こと。


## ラウンド16: Phase 2 の frame 述語を定義（成功）

```lean
def SameResources (a b : State) : Prop :=
  a.peRegisters = b.peRegisters ∧ a.l1bm = b.l1bm ∧ … （全16フィールド、hazardClock を除く）
```
と、その nop インスタンス `wholeMachine_nop_sameResources`。838 jobs 成功。

Phase 2 の命題は「ある行が成功したとき、`SameResources` の各成分のうち footprint が触れないものが不変」
という形で書ける。次は `.mv` と `.pe` について同じ形を証明する。
`.pe` は `executeIntegerProducerInstructionLine` の入れ子実行器を辿る必要があり、ここが Phase 2 の本体。


## ラウンド17: MV 行の issue 失敗を証明（成功）

PE 行と同じ構成で MV 行にも通した:
- `executeHazardAwareNormalizedLineCore_mv_issue_failure`（core レベル）
- `wholeMachine_mv_issue_failure`（`show` → `rw` ラッパー簡約 → `exact`）

838 jobs 成功。これで `wholeMachine.step` は **`.pe` と `.mv` の両方で「issue 拒否 → `.failure`」** が
証明された。worklist の「issue 違反は legal を狭めず step の失敗にする」が両命令種で成立。


## ラウンド18: frame 述語の代数（成功）

`SameResources.refl` / `.symm` / `.trans` を追加（`unfold` + `aesop`）。838 jobs 成功。
これでプログラム全体に frame を合成できる（行ごとの frame を `trans` で連結する）。

累計: 21 定理 + `SameResources`。Phase 1 完了相当、Phase 2 は述語と nop インスタンスまで。
次は `.mv`（転送 nop）の frame、続いて `.pe` の frame。`.pe` は入れ子実行器の列挙が必要で本体。


## ラウンド19: Phase 2 の作業分解（コード読解）

`Footprint.lean` の `UnitResource` と `State` フィールドの対応を整理する。これが `.pe`/`.mv` の
frame 証明で「どのフィールドを除外して `SameResources` を主張するか」の根拠になる。

| UnitResource | 変更しうる State フィールド |
|---|---|
| `alu` / `mau` / `forwarding` | `peRegisters`（ALU/MAU 出力）, `forwarding`, `forwardingValid` |
| `matrix` | `matrixRegisters`, `peRegisters`（matrix read 経由の writeback） |
| `l1bm` | `l1bm` |
| `l1bmTurnaround` | `l1bmTurnaround`, `l1bmTurnaroundValid` |
| `l2bm` / `mv` | `blockMemory`, `pendingMv`, `mvCompletedTags` |
| `maskRegisters` / `maskControl` | `maskDirective`, `peRegisters`（OMR） |
| `bar` / `t` | `peContext` |
| `lbf` | `forwarding` |
| `hazardClock` | `hazardClock`（常に進む。`SameResources` から除外済み） |

### frame 証明の型（次に書く定理）
行 `l` と resources 集合 `S` について:
```
∀ s next, wholeMachine.step l s = .ok next →
  SameResourcesExcept S s.machine next.machine
```
`SameResourcesExcept` は `SameResources` の各成分のうち `S` が含まないものだけを要求する述語。
今回の `SameResources`（全資源）は `S` が空の場合に相当し、nop で証明済み。

### 具体的な次の一歩
1. `SameResourcesExcept` を定義（`SameResources` を成分ごとに選べる形にする）
2. `.mv`（transfer nop）について `S = {hazardClock}` で frame を証明
3. `.pe` について `S = footprint の unitWrites` で frame を証明（本体）


## ラウンド20: mv-nop の step 等式（State レベル、成功）

```lean
theorem executeNormalizedLine_mvnop (transfer : NormalizedMv) (state : State)
    (nop : transfer.kind = .nop)
    (accepted : checkParsedTopLine (Issue.InstructionLine.mv transfer).toParsed = true) :
    executeNormalizedLine (.mv transfer) state
      = .ok { state with hazardClock := state.hazardClock + 1 }
```
838 jobs 成功。hazard-aware 層より下（`State`）で frame を積む方針の第1号。
次は同じ層で `.pe` の step 等式（`executeIntegerProducerInstructionLine` の分岐を落とす）に進む。


## ラウンド21: frame 述語の射影補題（成功）

`SameResources.peRegisters_eq` / `.l1bm_eq` / `.blockMemory_eq` / `.forwarding_eq` を追加。
838 jobs 成功。`SameResources` から個別フィールドの等式を取り出す部品で、
Phase 2 の frame 証明（`SameResourcesExcept` を作る代わりに必要な成分だけ射影する方針）で使う。


## ラウンド22: Phase 2 本体をサブエージェントで前進（検証済み）

`ProofsLean/FrameStep.lean`（1115行、59定理）を独立検証: `lake build ProofsLean.FrameStep` → 839 jobs 成功、
`sorry`/`admit`/`native_decide`/`axiom` なし。ルートに import して `lake build ProofsLean` → **850 jobs 成功**。

主要結果:
- `executeIntegerProducerInstructionLine_pe_plainIntegerALU`: plain 整数 ALU 行の step 等式
  （`.ok { nextPEs with hazardClock += cost, l1bmTurnaroundValid := false }`）
- `executeIntegerProducerLineAtPEs_frame`: **式に依存せず** `l1bm`/`blockMemory`/`dar`/`matrixRegisters` 不変
- `executeNormalizedLine_pe_peRegisters_noforward`: noforward 行は `peRegisters` を変えない
- forwarding は per-PE でのみ特徴づけ（無条件 frame は **偽**）

### 重要な負の結果（2件、footprint モデルの欠陥）
1. `normalizedLineFootprint_pe_plainIntegerALU_omits_l1bmTurnaround`:
   plain ALU 行は `l1bmTurnaroundValid := false` を設定するのに、footprint は `.l1bmTurnaround` を含まない。
2. `normalizedLineFootprint_pe_noforward_omits_forwarding`:
   `.noforward` 行は `forwarding pe` を書き換える（無効スロットが poison 化）のに、footprint は
   `.issueControl` しか挙げない。

→ 「成功した step の変更は footprint 内」という素朴な主張は、**現行の実行器と footprint の組では偽**。
   `l1bmTurnaroundValid` を frame から除外するか footprint に追加するか、noforward の forwarding 更新を
   footprint に含めるかの決定が必要。


## ラウンド23-24: footprint 整合と Phase 2 の field frame（検証済み）

独立検証: `lake build ProofsLean` → **851 jobs 成功**。`sorry`/`admit`/`native_decide`/axiom なし。
`ProofsLean/FootprintReconciled.lean` は 366 行。

### Footprint.lean の意味論的修正
1. `parsedOpUnitWrites .noforward` に `.forwarding` を追加
2. 新 `peLineFootprint`: すべての `.pe` 行に `.forwarding`、`noforward` を含まない行に `.l1bmTurnaround`

### 証明された frame（State レベル）
- `executeNormalizedLine_pe_plainIntegerALU_field_frame`: 11 フィールド不変 + `l1bmTurnaroundValid = false` + clock +1
- `executeNormalizedLine_nop_field_frame`, `executeNormalizedLine_mv_field_frame`
- `executeNormalizedLine_pe_plainIntegerALU_pe_stage`: 行の成功から per-PE walk の成功を導出

### 反例の反転
`..._omits_...` 3 本（+ 強制された補助1本）を `..._names_...` に置換。

### 残るギャップ
1. 無条件 `.ok` 等式は **per-PE 読み出し成功**で阻まれる（`.poison` 読みは `.failure`）
2. `peContext`（BAR 宛先なしの ALU 行）は未形式化
3. hazard-aware 層への持ち上げ（`Id.run do` の成功反転）
4. **machine.rs の fast path は `$lbi` を更新しない** — Lean 実行器は slow path 準拠。viz 側で要確認


## ラウンド24: Phase 3 完了（Welcome の `.unknown` 除去）

独立検証: `lake build ProofsLean` → **852 jobs 成功**。`WelcomeComplete.lean` 685行、`sorry` 等 0件。

- クラス: `IsWelcomeLine line := line = .pe [welcomeExpr 0] ∨ line = .pe [welcomeExpr 8]`
  （`answer.vsm` の2行そのもの。既存の `Issue.plusOneParsedAt` を再利用）
- 主定理: `wholeMachine_welcome_never_unknown`, `wholeMachine_welcomeExprLine_never_unknown`,
  `wholeMachine_welcomeLine_never_unknown`, `welcomeAnswer_lines_never_unknown`,
  `welcomeReachable_step_never_unknown`
- **残る仮定なし**: すべての `HazardAwareState` で成立（到達可能性も forwarding 解決も仮定しない）。
  ソースが LM0 の直接 `.mem` 読みなので `readWithForwarding` が全域的。
- 注意: ソース文字列→`ParsedExpr` のパースは未形式化。値の正しさや Rust 一致は主張しない。

→ Phase 3 の「Welcome 行で `.unknown` を消す」は達成。次は Phase 4（実機モデルでの `Optimal`）。


## ラウンド24-25: Phase 4 は未完了（Stage 1 のみ、sealed machine）

独立検証: `lake build ProofsLean` → **854 jobs 成功**。`WelcomeValue.lean` / `WelcomeOptimal.lean` に sorry 等なし。

### 達成（Stage 1、ただし制限付き）
`welcomeAnswer_correct : Correct welcomeSealedMachine welcomeSpec welcomeAnswer`

- `welcomeSealedMachine`: `State := MNCore.State`（`HazardAwareState` ではない）、
  `step := executeNormalizedLine` で非 `.ok` を `none` に落とす、`legal := True`
- **制限**: `wholeMachine.step` の issue/アドレスモード/PEハザード/ブロックハザード検査と
  `.unknown` 箇所を封じている。ハザード履歴なし
- 仕様: 16語の `BitVec 32`、`toNat ≤ 50`、全PEのLM0が同一、LM1/GRF/T/マスクはゼロ、
  観測PE 0 の LM1 語 i = 入力 i + 1（ラップ加算）
- 実 4096-PE walk・実 4サイクル `.long` 経路を使用（旧 `PlusOne` 限定モデルではない）

### 未達（Stage 2/3）
`SymbolicBoundCertificate` も `LowerBound` も `Optimal` も**存在しない**。
ブロッカーは base-0 の1行プログラムを反証するための「未書き込みの高位 LM1 語（8..15）の保存」。
base-0 の frame 補題が閉じず、壊れたビルドを残さないため撤回された。空プログラムと base-8 の1行は射程内。

→ **`Optimal wholeMachine ...` は主張しない。Phase 4 は未完了。**


## ラウンド25: Stage 2（Welcome クラス）は閉じた。無制限の LowerBound は未達

独立検証: `lake build ProofsLean` → **855 jobs 成功**（docstring 修正後 842 jobs 再ビルド）。
`WelcomeLowerBound.lean` 532行、sorry 等 0件。

### 証明されたこと
- `welcomeEmpty_not_correct`（空プログラム）
- `welcomeAtMostOneWelcome_not_correct`（`IsWelcomeLine` 高々1行）
- `welcomeWelcomeLine_anyBase_not_correct`（**任意の base** の `iinc` 1行。base 0/8 に限らない）
- `welcomeLowerBound_one` と `welcomeBoundOneCertificate`
- **`welcomeOnlyClass_does_not_cover`**: bound 2 の certificate を Welcome クラスに制限すると `covers` が偽（`.nop 1` が反例）
- `welcomeLowerBound_two_iff_rejects_short_lines`: `LowerBound … 2` は「任意の1行を反証できる」ことと同値

### 未達（Phase 4 の残り全部）
```
∀ line : InstructionLine, InstructionLine.cost line < 2 →
  ¬ Correct welcomeSealedMachine welcomeSpec [line]
```
これが `LowerBound … 2` と同値で、これが済めば `Optimal` は `welcomeAnswer_correct` から直ちに従う。
任意 `.inc` LM1 宛先クラスへの拡張は、executor の一般的な逆解析と未書き込み語の基数論証が必要で未着手。

### 整合性の修正
`WelcomeOptimal.lean` の docstring が存在しない `two_lineLowerBound` / `welcomeAnswer_optimal` を
宣伝していたため、**未証明であることを明記する記述に修正**した（ビルド再確認済み）。


## ラウンド26: 無制限1行反証は未完成（ギャップを Lean で同値化）

独立検証: `lake build ProofsLean` → **856 jobs 成功**。`WelcomeLowerBoundTwo.lean` 550行、sorry 等 0件。

### 証明された範囲
`.nop`（任意 count）、`.mv`（任意 transfer）、issue 拒否 `.pe`、wait pending、未対応 ALU、
非対応 producer、全 noforward（空を含む）、`[welcomeExpr base]`（全 base）を反証。
加えて `welcomeLowerBound_two_of_unrefuted`（条件付き LowerBound 2）。

### 残る唯一の義務（Lean で同値化済み）
```
WelcomePEUnrefuted exprs （受理・wait なし・対応 producer・全 noforward でない・Welcome 1行でない）
welcomeLowerBound_two_iff_unrefuted :
  LowerBound ... 2 ↔ ∀ exprs, WelcomePEUnrefuted exprs → ¬ Correct ... [.pe exprs]
```
非空性の証人 `welcomeImmediateOneExpr` も提示。この同値により「ギャップを弱めていない」ことが保証される。

### 次に必要な証明
全ゼロ入力で単一 LM1 writer が16語を埋められないこと:
`.word`/`.long` は4サイクルで最大8語、`.double` は生ソース語（初期状態で0）を index 2,3 に入れる。
`.double`/マスクの場合分けが難所で未形式化。

→ **`Optimal` は依然として存在しない。Phase 4 は未完了。**


## ラウンド27: 無制限1行反証を「二面」に縮約（LowerBound 2 は未達）

独立検証: `lake build ProofsLean.WelcomeBoundTwo` → **845 jobs 成功**、
`lake build ProofsLean` → **856 jobs 成功**。新規 `ProofsLean/WelcomeBoundTwo.lean`
637行、sorry/admit/native_decide/新規 axiom は 0 件（docstring の注意書きのみ）。

### 証明されたこと（`ProofsLean/WelcomeBoundTwo.lean`）
- `evaluateBus_value_low` / `evaluateBus_value_low_zero`: ALU バスの下位64bitは
  「先頭オペランドのコピー」か「0」(reduced) であり、計算結果にはならない。
- `unpackALUBus_two_zero` / `unpackALUBus_three_zero` /
  `flushBus_low_zero` / `parsedOutputAfterFlush_low_zero`: `.double` 書き込みの
  データ語2・3はフラッシュ後も0。
- `welcomeZero_readDirectAccess_zero`, `welcomeZero_pack_readDirectAccess_zero`:
  全ゼロ初期状態では全バンクの読み出しが0。
- `prepareParsedMaskedWriteWithForwarding_memory_eq_flush`（flush 選択を残した一般形）と
  `prepareParsedMaskedWriteWithForwarding_data_two_three_zero`:
  メモリ source が0バスなら prepared ALU write の data 2,3 は0。
- `writeWordsMasked_double_block_two` / `writeWordsMasked_double_block_third` /
  `commitParsedMaskedWrites_lm1_word_zero`: 4アライン `.double` ブロックの3語目は
  bus index 2 でのみ書かれ、old=0 かつ data₂=0 なら commit 後も0
  （`commitParsedMaskedWrites_cons` と `welcomeCommitStep` を追加）。
- `welcome_not_correct_of_word_zero`: 全ゼロ入力でPE0 LM1の語が1つでも0なら反証。
- `welcome_not_correct_of_inputIndependentLM1`: 全ゼロ入力と全5入力でPE0 LM1出力が
  等しいなら反証（仕様はそれぞれ1と6を要求）。
- `welcomeLowerBound_two_of_allWordsChanged`: 16語すべてを書き換えない行は反証。
- `welcomeLowerBound_two_of_residual` と `welcomeLowerBound_two_iff_residual`:
  残差クラス `WelcomePEResidual`（受理・非自明・全ゼロ入力で16語すべて非零・
  出力が入力依存）の反証と `LowerBound 2` が**同値**。

### 残る義務（Lean で明示）
`WelcomePEResidual → ¬ Correct …`、すなわち「16語すべてを入力依存データで書く行」の反証。
executor 側の欠落は `WelcomeWriteProvenance`（PE0 のレジスタファイルが prepared write 列の
commit であること）として `Prop` で明示。仮定はしていない。
未反証の producer/width は `WelcomePEResidual` の docstring に列挙:
整数段の `.alu`/`.immediate`/`.zero`/`.matrixRead`（幅 `.word`/`.long`/`.double`）、
`.mau` の各ファミリ、`.matrixWrite`、`.l1bm`、`.l2bm`。

→ **`Optimal` は依然として存在しない。Phase 4 は未完了。**


## ラウンド28: executor 接続を証明（`WelcomeWriteProvenance`）。形状義務が残る

独立検証: `lake build ProofsLean` → **858 jobs 成功**。`WelcomeProvenance.lean` 691行、実 sorry なし
（唯一の "sorry" は docstring 内の文言）。

### 証明
- `welcomeWriteProvenance_of_plainIntegerALU`: plain 整数 ALU クラスについて、成功した `.pe` 行の後
  PE 0 のファイルが `commitParsedMaskedWrites` の形になる（新規 walk 補題が必要だった）
- `.double` ブロックのコピー論証: `commitParsedMaskedWrites_lm1_word_zero_of_double`、
  `prepareParsedMaskedWriteWithForwarding_data_two_three_zero_of_low_zero`
  （data 語2,3 は**第1オペランド**の下半分のみに依存 → 任意の op/丸めをカバー）
- `welcomeAnswer_score`, `welcomeAnswer_optimal_of_lowerBound`（**条件付き**）

### 未証明（Lean の Prop として10個）
`WelcomePEPlainDoubleShapeObligation`, `WelcomePEOtherDoubleShapeObligation`,
`WelcomePEMatrixRead`/`MatrixMAU`/`FloatMAU`/`MatrixWrite`/`L1ToPE`/`L2BM` `DoubleObligation`,
`WelcomePENarrowCoverageObligation`, `WelcomePEConstantInputIndependentObligation`

→ `welcomeLowerBound_two` も `welcomeAnswer_optimal` も**存在しない**。`Optimal` は主張しない。
ブロッカーは executor ではなく **write shape**（4サイクル全てが double 分岐を取るか、2人目の LM1 writer が無いか）。


## ラウンド29: 形状分解が**不健全**だったことが判明（重要な訂正）

独立検証: `lake build ProofsLean` → **859 jobs 成功**。`WelcomeShapes.lean` 344行、7定理。

### 判明した問題
`WelcomeProvenance.lean` の10個の形状義務は、**書かれたままでは証明できない**:
1. `WelcomePEResidual` を仮定しているが、その非空性こそが証明対象（循環）
2. residual は「data 語2 = 0」を含意しない。`.fixed .msb1` を `.word` 精度で第1オペランドにすると
   `low = lane ++ lane` で bus 語2,3 が `0x80000000` になる。それでもメモリ第2オペランドなら出力は入力依存
3. `WelcomePENarrowCoverageObligation` は任意の `writes` を量化するため強すぎる

### それでも得られたもの
`parsedOperand_toDirectMemoryAccessMode_aligned`（全 direct-memory 宛先が幅で整列）など4件は証明済み。

### 次の方針（要変更）
形状分解を捨て、**直接の値論証**に切り替える: 「全ゼロ入力で PE-0 の LM1 のどれか1語が 1 でない」。
`.double`（語2が第1オペランド下半分）、`.word`/`.long`（最大8語しか書かない）、定数行（全5入力で不一致）を
値のレベルで場合分けする。

→ `welcomeLowerBound_two` / `welcomeAnswer_optimal` は存在しない。`Optimal` は主張しない。


## ラウンド30: 健全な還元に成功（循環と偽の主張を修復）

独立検証: `lake build ProofsLean` → **860 jobs 成功**。`WelcomeValueBound.lean` 1077行・44定理。

### 修復
ラウンド29で不健全と判明した分解を捨て、**非空で健全な**義務に還元:
```lean
def WelcomePELm1WriteShapeObligation : Prop :=
  ∀ expressions, WelcomePEUnrefuted expressions →
    WelcomePEDoubleCopyShape ∨ WelcomePENarrowShape ∨ WelcomePEInputIndependent
theorem welcomeLowerBound_two_of_lm1WriteShapes (h) : LowerBound … 2
theorem welcomeAnswer_optimal_of_lm1WriteShapes (h) : Optimal … welcomeAnswer   -- 条件付き
```
- `WelcomePEResidual` を仮定しない（循環を除去）
- `.double` の結論を「data₂ = 0」から **「word 2 がコピー」(`IsWelcomeCopy`、`0x80008000` の部分マスク)** に修正

### 新規に無条件で証明
- `welcome_not_correct_of_word_ne_one`
- コピー代数 → `commitParsedMaskedWrites_lm1_word_two_isWelcomeCopy` → `welcome_not_correct_of_doubleCopyShape`
- 数え上げ → `exists_uncovered_of_windows`（2語窓4本では16語中8語しか覆えない）→ `welcome_not_correct_of_narrowShape`
- **`.fixed .msb1` の反例ケースを閉じた**: `prepareParsedIntegerALUExprCycle_alu_direct_double_copy_of_fixed`
- `welcomeLm1Writer_unique`（`writesUnique` から、LM1 writer は高々1式）

### 残る義務
`WelcomePEPlainShapeObligation`（8つの非 direct 分岐の宛先解析、幅共有、4096-PE 持ち上げ）と
`WelcomePEOtherShapeObligation` + 6族（`.matrixRead`/`.mau`/`.matrixWrite`/`.l1bm`/`.l2bm`）。

→ `welcomeLowerBound_two` も `welcomeAnswer_optimal` も無条件には存在しない。`Optimal` は主張しない。


## ラウンド31: plain 形状を2つの Prop まで還元

独立検証: `lake build ProofsLean` → **861 jobs 成功**。`WelcomePlainShape.lean` 1323行、実 sorry なし。

### 閉じたもの
- **link 1**: 8つの非 direct 分岐すべての厳密なリスト等式
- **link 2 の半分**: `directDestinationBankWidth?` と `toDirectMemoryDestination?_bankWidth`
  （幅はサイクル非依存、アドレスだけがサイクル依存）
- **data 半分**: `prepareParsedMaskedWriteWithForwarding_data_two_isWelcomeCopy_of_read_copy`
  （memory/fixed/forward 源と flush 選択に対して一様）
- **窓の記帳**: `lm1WindowsOfWrites` と nil/empty/append 補題

### 残る2つの Prop
1. `WelcomePEPlainStepShapeExceptImmediate` — 4サイクル畳み込み + `writesUnique` 橋渡し +
   4096-PE 持ち上げ（機械的だが 250〜500 行の配管）
2. `WelcomePEPlainImmediateDoubleObligation` — immediate の `.lm1 .double` 宛先に対する入力非依存性

### 重要な訂正
`.immediate` のバスは `⟨word, word⟩` で、3語目のデータは **sparse の値によらず payload**（kernel の `decide` で確認）。
したがって逃げるケースは「非 sparse のみ」ではなく **`.immediate` かつ `.lm1 .double` 宛先のすべて**。

→ `welcomeLowerBound_two` は依然として存在しない。`Optimal` は主張しない。


## ラウンド32（中間）: 構造的発見で作業量が縮小

`ProofsLean/WelcomePlainClose.lean`（1405行、ビルド 851 jobs 成功、エージェントは継続中）。

### 構造的発見
issue checker の `groupsUnique` により、**未反証の plain `.pe` 行は高々1行**。
plain 行（`.alu`/`.zero`/`.immediate`）はすべて issueGroup `.alu` で、`projectLine` が位置ごとに
異なる id を割り当てるため、2行あれば `groupsUnique` に反する。空行・全 noforward は既に除外済みなので、
plain な未反証行は **`[e]` ただ1つ**。

→ 複数式の fold、`writesUnique` 橋渡し、式をまたぐ forwarding が**すべて不要**になり、
行全体の prepared list は1回の4サイクル fold になる。

### 消化済み
- `WelcomePEPlainImmediateDoubleObligation`（`welcomePEPlainImmediateDoubleObligation`）
- 正確な prepared list 抽出（`welcomeIntegerPrep`, `executeIntegerProducerLineAtPEs_prepared`, `welcomeSealed_pe_prepared`）
- LM1 書き込みの数え上げ・provenance 補題

### 残り
`WelcomePEPlainStepShapeExceptImmediate` — 9分岐の per-cycle 解析（P1/P2/P3）、4サイクル fold、
`Lm1WritesDoubleCopy`/`Lm1WritesNarrow` の分割。

→ `LowerBound 2` も `Optimal` も未主張。


## ラウンド32（最終）: plain 側は1 Prop 消化、残りは 1 Prop + 6族

独立検証: `lake build ProofsLean` → **862 jobs 成功**。`WelcomePlainClose.lean` 1671行、実 sorry なし。

### 消化
`WelcomePEPlainImmediateDoubleObligation`（`welcomePEPlainImmediateDoubleObligation`）。
`groupsUnique` による単一行還元 + 4サイクル準備がレジスタファイル非依存 + `commitParsedMaskedWrites_lm1_congr`。

### 枠組みとして証明済み（無条件）
`plain_legal_length_le_one`, `welcomeSealed_pe_prepared`, `welcomeIntegerPrep_inv`,
`welcomeIntegerPrep_single_plain_eq`, `prepareParsedIntegerALUExprCycles_four`,
`updateParsedIntegerALUForwardingCycle_frame`, `lm1Destinations_unique_positions`,
`mapM_lm1_count_le`, `constantTargets_lm1_count_le`

### 残る義務（全2つ）
1. `WelcomePEPlainStepShapeExceptImmediate` — 9分岐の per-cycle 解析（LM1 write の provenance、
   `.double` の data 語2 コピー、チャンクあたり LM1 write 高々1）
2. 非 plain の6族（matrixRead / matrixMAU / floatMAU / matrixWrite / L1ToPE / L2BM）

→ `LowerBound 2` も `Optimal` も存在しない。


## ラウンド33: **`WelcomePEPlainShapeObligation` を証明**（plain クラス完成）

独立検証: `lake build ProofsLean` → **863 jobs 成功**。`WelcomePlainStep.lean` 約2890行、実 sorry なし。

```lean
theorem welcomePEPlainStepShapeExceptImmediate : WelcomePEPlainStepShapeExceptImmediate
theorem welcomePEPlainShapeObligation : WelcomePEPlainShapeObligation :=
  welcomePEPlainShapeObligation_of_two welcomePEPlainStepShapeExceptImmediate
    welcomePEPlainImmediateDoubleObligation
```

- `Lm1ChunkFacts`（宛先 provenance、`.lm1 .double` の data 語2コピー、チャンクあたり LM1 write 高々1）を
  9分岐すべてで証明（10個の分岐反転補題 + ケース木）
- `destResolves_width_eq`（幅はサイクル非依存）、`lm1WritesShape_of_chunks`（4チャンクから
  `Lm1WritesDoubleCopy ∨ Lm1WritesNarrow`）
- plain クラスの per-branch 義務は**ゼロ**

### 残る義務（6族のみ）
`WelcomePEOtherShapeObligation` とその特殊化:
`WelcomePEMatrixRead` / `MatrixMAU` / `FloatMAU` / `MatrixWrite` / `L1ToPE` / `L2BM` `ShapeObligation`

→ これらが片付けば `welcomePELm1WriteShapeObligation_of_two welcomePEPlainShapeObligation other`
で `WelcomePELm1WriteShapeObligation` → `LowerBound 2` → `Optimal` に到達する。
現時点で `LowerBound 2` も `Optimal` も存在しない。


## ラウンド34: 6族は行ローカルに閉じない → 統合還元に方針転換

独立検証: `lake build ProofsLean` → **864 jobs 成功**（`WelcomeL12Shape.lean` 1169行を配線）。

### 構造的発見（両エージェントが独立に確認）
`WelcomePEWriteShape` は行全体の `.lm1` 宛先を制約するが、`welcomeLm1Writer_unique` により
LM1 を書く行は高々1つで、**それが当該 family の行とは限らない**。
例: `.matrixWrite` は PE `.lm1` を書かないので、`[matrixWrite, alu→lm1]` では ALU 行が唯一の writer。
`.l2bm` も同様（`executeParsedSharedBlockProducers_peRegisters` で PE レジスタ不変）。

### L1/L2 側で得られた行レベル事実（無条件）
- `l1ToPEBusAt_welcomeInitialState`: 初期状態で L1BM→PE バスはゼロ
- `l1ToPE_data_word_two_isWelcomeCopy` / `parsedOutputAfterFlush_l1ToPEBusAt_zero`
- `l1ToPEWrites_doubleCopy` / `l1ToPEWrites_narrow`（4サイクル書き込みの形状分割。ただし `.double` の
  4整列が `toDirectMemoryAccessMode?` から未導出 — Nat の整除補題が欠けている）
- サイクルループ展開に名前が付いた: `writeCycles`, `writeCycles_four`, `writeCycles_cons`, `writeCycles_nil`

### 統合還元の設計
行レベルの組立補題を**1回だけ**証明し、6族をそのインスタンスにする。
必要なインターフェース（L1/L2 側からの要求、MAU 側に伝達済み）:
(a) 中間段4つの `lm1` frame、(b) 整数段のリストレベル provenance、(c) `executeParsedL1ToPEAtPEs` の外側1歩展開

→ `LowerBound 2` も `Optimal` も未主張。


## ラウンド34-35: matrixRead の行形状を証明。**6族分解が不完全**と判明

独立検証: `lake build ProofsLean` → **865 jobs 成功**（`WelcomeMAUShape.lean` 1050行を配線）。

### 証明
- `prepareParsedMatrixReadExprCycles_zeroShapeStatic`: 零状態の matrix-read 行は
  `Lm1WritesDoubleCopy ∨ Lm1WritesNarrow`
- `prepareParsedIntegerMatrixReadLineExpression_matrixRead_shape`（行組み立てに直結）
- `matrixWriteStage_lm1_frame` / `executeParsedMatrixMAUAndWrites_lm1_frame_of_noMatrixMAU`:
  `.matrixWrite` 行は**決して唯一の LM1 writer にならない**

### 重要（F5）: 6族分解は不完全
`parsedExprIsSupportedPELineProducer` は `.noforward` と `.l1bm` の
`mwrite`/`m4write`/`gather`/`reduce`/`reduce4` も受理する。したがって
`[noforward, alu→lm1]` のような行は非 plain かつ6族のどれにも属さず、
**6族を全部証明しても `welcomePELm1WriteShapeObligation_of_two` は埋まらない**。
→ 7番目（8番目）の義務が必要か、「plain または no-write」クラスへの強化が必要。

### その他の欠落
F1 行組み立て、F2 整数段の負の provenance、F3 float-MAU 行形状、F4 matrix-MAU 行形状。


## ラウンド35: F5（分解の穴）を修正 — 網羅分割を証明

独立検証: `lake build ProofsLean` → **866 jobs 成功**（`WelcomeGapShape.lean` 1065行を配線）。

### 網羅分割
`supportedProducer_shape_cases`（18分岐）と `supportedProducer_shape_cases_of_checked`（14分岐）。

**F5 の記述の訂正**（実際の述語から判明）:
- `.matrixWrite` は6族の1つなのに13項目リストから漏れていた
- `.wait tag` も受理される（未完了時のみ `.unknown`。未反証行では不活性）
- `.alu` は無条件に受理されるため、非 plain の `.alu` は block float だけでなく
  msl/msr、float-relu 名、`lrelud`/`lreluo`/`ilrelud` も含む

### 消化したもの
- `.noforward` 行は書き込みを準備しない
- `.l1bm` の5形式は PE 不活性（`executeParsedSharedBlockProducers_peRegisters`）
- `executeIntegerProducerInstructionLine_pe_peRegisters_of_inert` → `welcomePEInertLine_shape`

### 訂正後の集約
`welcomePELm1WriteShapeObligation_of_nine : plain + 6族 + specialALU + mixed → WelcomePELm1WriteShapeObligation`

### 残る義務
1. `WelcomePESpecialALUShapeObligation`（msl/msr、float relu、block float）
2. `WelcomePEMixedPlainInertShapeObligation`（LM1 writer が plain 行で他が不活性な場合の行組み立て）
3. F1–F4（行組み立て、float-MAU/matrix-MAU 行形状、整数段 provenance）

→ `LowerBound 2` も `Optimal` も未主張。


## ラウンド35-36: F1（行組み立て）の骨格を証明

独立検証: `lake build ProofsLean` → **867 jobs 成功**（`WelcomeAssembly.lean` 1138行を配線）。

### 証明
1. 段の剥がし: `executeIntegerProducerInstructionLine_pe_stages_exists`（6つの中間状態と各段の等式）
2. 空フィルタ時の恒等性（MSL/MSR、float-relu、block-float、L1ToPE、matrix-MAU、共有ブロック）
3. **clean-line 組み立て**: `welcomePE_line_commit_of_clean`。全 plain 行が含まれる（`welcomePE_line_commit_of_plain`）
4. **一般組み立て**: `welcomePE_line_stage_commit`（6つの段ごとの commit 義務から、PE0 の commit を導出）
5. **`.lm1` 代数**: `commitParsedMaskedWrites_lm1_concat_of_only`（`.lm1` を書かないブロックは合成から落ちる）
6. `welcomePE_not_correct_of_noLm1Destination`（`.lm1` を名指す行が無ければ反証）

### 残る Props（段ごとの commit 義務、`.lm1` provenance/frame）
`WelcomePEIntegerFloatStageCommit`, `WelcomePEIntegerStageCommit`, `WelcomePEMslMsrStageCommit`,
`WelcomePEFloatReluStageCommit`, `WelcomePEBlockFloatStageCommit`, `WelcomePEMatrixMAUStageCommit`,
`WelcomePEL1ToPEStageCommit`, `WelcomePEIntegerStageLm1Provenance`, `WelcomePEIntegerStageLm1Frame`,
`WelcomePEStageLm1Frame`


## ラウンド36: 組み立て骨格の完成と、残る段义务の具体化

独立検証: `lake build ProofsLean` → **867 jobs 成功**（`WelcomeAssembly.lean` 1212行・52宣言）。

### 追加で証明
- `writeParsedMslMsrDestination?_lm1_of_ne`（MSL/MSR・float-relu・float-MAU が共有する per-destination `.lm1` frame）
- `executeParsedSharedBlockProducers_lm1_frame`（無条件）
- `welcomePE_line_lm1_frame` と `welcomePE_not_correct_of_noLm1Destination`

### 残る段義務の技術的障害（特定済み）
局所再帰子 `writeDestinations`/`runCycles` の反転で、
`rw [...]` の後に `Bind.bind` の do ブロックが残り `split` で分割できない。
**cons 等式と `= none ↔ = none` 補題を別々に用意してから帰納する**のが正解。

→ `LowerBound 2` / `Optimal` は未主張。F5 のギャップは修正済み（`WelcomeGapShape.lean`）。


## ラウンド36-37: 段義務 5/6 を証明

独立検証: `lake build ProofsLean` → **868 jobs 成功**。`WelcomeStageCommit.lean` 1724行・50宣言。

### 証明（6つのうち5つ）
`welcomePEMslMsrStageCommit` / `welcomePEFloatReluStageCommit` / `welcomePEL1ToPEStageCommit` /
`welcomePEIntegerFloatStageCommit` / `welcomePEBlockFloatStageCommit`

MSL/MSR・float-relu・block-float は空フィルタ限定ではなく**全状態・全式**で証明。

### ラウンド36の障害の解決法（再利用可能）
- 親 `def` を `unfold` しない。**局所再帰子の equation lemma を名前で `rw`**
- 本当のブロッカーは `Bind.bind` ではなく **`Id.run`/`pure` の残り**。`dsimp only at executed` で剥がす
- lowered write の分割は本文と同一構文の `cases lowered : <term>`
- `some` 分岐の再帰呼び出しは**定義的帰属**（`have tail := executed`）で取り出す

### 未証明
`WelcomePEMatrixMAUStageCommit` — 5つの再帰子等式（宛先ループ、4PE アキュムレータ、4サイクル、
MAB 再包装 + `commitParsedMatrixMAUPEState` の2射影、1024座標 walk）が未整備。


## ラウンド37: 特殊 ALU（msl/msr）の行形状を証明

独立検証: `lake build ProofsLean` → **869 jobs 成功**（`WelcomeSpecialShape.lean` 745行を配線）。

### 証明
- MSL/MSR の行形状は**閉じた**: `welcomePEMslMsrCyclesShape`（読み出し仮定不要。
  `mslMsr_output_word_two_copy` により出力3語目は常にコピー）
- `writeParsedMslMsrDestination?_facts`: 静的 `.lm1` 幅・4整列・3語目コピー
- 3語目コピーの補題群（flush は AND のみなのでコピーを保つ、relu は sourceA の下半分を保つ、
  block float `.d/.f/.g` は3語目ゼロ）

### 残る named Props（6つ）
`WelcomePEMslMsrExecutorExposure`（実行器の `sourceAt` が補助 match `executeParsedMslMsrAtPE.match_3`
にコンパイルされ、手書きの写しでは `rw` が発火しない）、float-relu の fold / ゼロ入力読み出し / flush、
block-float の MAB fold / half ゼロ入力。

### `WelcomePESpecialALUShapeObligation` 自体は未達
LM1 writer が別行になるケースを含むため、行組み立てと `.lm1` frame が必要。

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド37-38: relu/block-float の3つを証明、2つは**反例つきで偽**と判明

独立検証: `lake build ProofsLean` → **871 jobs 成功**（`WelcomeReluBlockShape.lean` を配線）。

### 証明
- `welcomePEFloatReluFlushCopy`
- `welcomePEFloatReluCyclesShape`（msl/msr の fold の逐語的類推）
- `welcomePEBlockFloatHalfZeroInputCopy`（`parsedBlockFloatMab_h_zero`）

### 偽と判明（kernel 検証済みの反例）
1. `WelcomePEFloatReluZeroReadCopy` — **偽**（`not_welcomePEFloatReluZeroReadCopy`）。
   精度 `.f`、ソース `.fixed .l2bid`、`context.group = 1` で、読み出しバスが
   `⟨0x0000000200000002, 0x0000000200000002⟩`、コピー語が `2` で `IsWelcomeCopy` でない。
   任意の文脈と任意の PE を量化していたのが原因。PE 0 に限れば真（PE 0 の `.fixed` は 0 か msb1 のみ）。
2. `WelcomePEBlockFloatMabShape` — **そのままでは閉じない**（`parsedBlockFloatMab_h_third_word_not_copy`）。
   `.h` 精度は入力レーン4-7から下半分を作るため、3語目がコピーにならない。
   出力バスのコピー仮定を足した版（`..._of_busCopy`）と `.d/.f/.g` 限定版（`..._of_precision_low_zero`）を証明。

→ どちらも「仮定の修正」が必要で、修正版は既に用意されている。


## ラウンド38: 段義務 6/6 完了、組み立てが無条件に

独立検証: `lake build ProofsLean` → **872 jobs 成功**（`WelcomeMatrixMAUCommit.lean` 645行を配線）。

### 証明
- `welcomePEMatrixMAUStageCommit` — 5つの再帰子等式（宛先ループ、4PE アキュムレータ、
  4サイクル、MAB 再包装 + `commitParsedMatrixMAUPEState` の2射影、1024座標 walk）
- **`welcomePEStageCommitForm`** — 6つの段義務すべて
- **`welcomePE_line_stage_commit_unconditional`** — F1 の行組み立てが**仮定なし**で成立

### 残る義務
- `.lm1` frame（`WelcomePEIntegerStageLm1Frame`、`WelcomePEStageLm1Frame`）
- `WelcomePEMslMsrExecutorExposure`
- float-relu / block-float の形状 Props（修正版）
- `WelcomePESpecialALUShapeObligation`
- 下界トラック本体

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド38: 修正版 Props と `.lm1` frame の大半を証明

独立検証: `lake build ProofsLean` → **873 jobs 成功**（`WelcomeFrameFix.lean` 1535行・49宣言を配線）。

### 証明
- `welcomePEFloatReluZeroReadCopy_at_welcomePE` — **PE0 に制限した修正版**（前回偽と判明した Prop の正しい形）。
  不足していた「lowering の do ブロックから sourceA を取り出す」補題（`lowerParsedFloatRelu?_sourceA_lowering`）を用意
- `welcomePEBlockFloatMabShape_of_busCopy_hyp` / `_lowPrecision` — **block-float の修正版2種**（元の Prop と同じ量化・結論なので下流は名前を変えるだけ）
- `welcomePEIntegerStageLm1Frame_corrected` — **修正仮定版**（float-MAU フィルタへの制約を追加）。旧仮定の実用ケース（フィルタ空）も包含
- `WelcomePEStageLm1Frame` の**5つのうち3つ**を無条件で証明（MSL/MSR、float-relu、block-float）。
  各々 destinations → cycles → PE → walk → filter の完全な帰納
- `welcomePEStageLm1Frame_of_residuals` — 残り2つから全体を導出

### 残り
`WelcomePEMatrixMAUStageLm1Frame` と `WelcomePEL1ToPEStageLm1Frame` の2つに縮小。

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド39: `.lm1` frame が無条件で完成

独立検証: `lake build ProofsLean` → **874 jobs 成功**（`WelcomeLm1FrameResidual.lean` 719行を配線）。

### 証明
```lean
theorem welcomePEMatrixMAUStageLm1Frame : WelcomePEMatrixMAUStageLm1Frame
theorem welcomePEL1ToPEStageLm1Frame   : WelcomePEL1ToPEStageLm1Frame
theorem welcomePEStageLm1Frame : WelcomePEStageLm1Frame :=
  welcomePEStageLm1Frame_of_residuals welcomePEMatrixMAUStageLm1Frame welcomePEL1ToPEStageLm1Frame
```
`WelcomePEStageLm1Frame` が**無条件**になった。`executeIntegerProducerInstructionLine_pe_lm1_frame` から消費可能なことも確認済み。

エージェントは brief の誤りも指摘: `writeParsedL1ToPEDestination?_lm1_of_ne` は存在しなかったため新規に証明。

### 残り（このトラック）
`WelcomePEIntegerStageLm1Frame` は**書かれたままでは導出不能**（float-MAU の書き込みが同段内で起きる）。
修正版と「float-MAU なし」版は既にある。行レベルの消費者は既に per-row の `noLm1` を受け取るので、
修正版から再導出するのが次の一歩。

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド39: 唯一 writer への橋を架橋（8 Props + 構造 → 行形状）

独立検証: `lake build ProofsLean` → **875 jobs 成功**（`WelcomeWriterShape.lean` 1194行・43宣言を配線）。

### 証明
- `.lm1` 代数（`.lm1` を含まないブロックは連結から見えない）
- `welcomePEWriteShape_of_commit_shape`（1つの書き込みリストから行形状）
- **`welcomePE_line_commit_of_integerOrInert`** — 整数段入力 + PE 不活性行の組み立て
- **`welcomeIntegerPrep_single_writer`** — 単一 writer の特徴づけ（`.noforward`/`.wait` は空リストを準備）
- インスタンス化: plain writer / matrixRead writer / `.lm1` 無し行 / 全不活性行
- **`welcomePELm1WriteShapeObligation_of_eight_and_structure`**: 8族 Props + 構造 → `WelcomePELm1WriteShapeObligation`

### 新たに判明した3つのブロッカー（`WelcomePEMixedPlainInertStructure` 内）
1. **マスクフラグの不一致** — 段は**行のフラグ**で準備するが、`plainRow_lm1_shape` は**行自身のフラグ**で述べられている。
   不活性行が masked `.mem`/`.bar`/`.omr` 宛先を持つと両者がずれ、`Legal` はそれを禁じていない
2. **mixed 行での immediate-double 除外**（全 plain 行の2入力比較しか無い）
3. `noforward* ++ [writer] ++ noforward*` のリスト分割が未形式化

### 未証明の行種別
float MAU（`.lm1` 形状が皆無）、matrix MAU、`.l1bm` の `.mem lm1` 宛先（`l1ToPEWrites_doubleCopy`/`_narrow` と
4整列の整除補題が未完成）

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド40: mixed 構造のブロッカー2つを消化、3つ目を分離。**元の構造は反証された**

独立検証: `lake build ProofsLean` → **876 jobs 成功**（`WelcomeMixedStructure.lean` 941行を配線）。

### 消化
1. **リスト分割**: `welcomeMixed_stageInput_split` + 実行器の fold（`prepareParsedIntegerMatrixReadLineExpressions_split`）
   + `welcomeMixed_integerPrep_single_writer`。`writeBanks` の nodup 成分も `LegalParsedLine.writesUnique` から導出
2. **mixed 行の immediate-double**: `welcomePEMixedImmediateDouble_inputIndependent`（2入力比較を行レベルで実施）

### 重要な発見: `WelcomePEMixedPlainInertStructure` は**偽**
`welcomePEMixedPlainInertStructure_forbids_immediateDouble` により、immediate-double の場合に
`notDouble` フィールドが偽になる。**構造の弱化が必要**（証明不足ではない）。

### 還元版と条件付き完全消化
- `WelcomePEMixedPlainInertStructureReduced`: `notDouble` を「(flagEq ∧ notDouble) ∨ 入力非依存」に置換
- `welcomePELm1WriteShapeObligation_of_eight_and_flagAgreement`: 8族 Props + `WelcomePEMixedPlainInertFlagAgreement` → 行義務
- `welcomePELm1WriteShapeObligation_of_eight_and_inertFlagsClear`: 不活性行が masked 宛先を持たない条件で**完全消化**

### 残る第3のブロッカー（仮定せず）
`WelcomePEMixedPlainInertFlagAgreement` — 段は**行のフラグ**を渡すが `plainRow_lm1_shape` は**行自身のフラグ**で述べられている。
writer のフラグが偽で、不活性行が masked `.mem`/`.bar`/`.omr` 宛先を持つときに限り失敗する
（`welcomeMixed_flagAgreement_fails_iff` で特徴づけ済み）。閉じるには自由フラグでの分岐解析のやり直しが必要。

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド40: float MAU 行形状（narrow 半分は無条件）

`ProofsLean/WelcomeFloatMAUShape.lean`（1240行・39宣言）を配線し、`lake build ProofsLean` → **877 jobs 成功**。

### 無条件で証明
- `executeParsedFloatMAUsAtPE_zeroNarrow_static` — `.double` でない静的幅なら `Lm1WritesNarrow`
- `writeParsedMAUDestinations?_widthCount` / `executeParsedFloatMAUCyclesAtPE_widthCount`
- 4整列（`directDestination_static_width`）

### 条件付き
`executeParsedFloatMAUsAtPE_zeroShape_static` — `WelcomePEFloatMAUHalfCycleCopy` を仮定すれば
`Lm1WritesDoubleCopy ∨ Lm1WritesNarrow`。cycle の16分岐のうち `.f`/`.d`/legacy は
`⟨output, 0⟩`（下位半分が文字通り0）で片付き、**`.h` の4分岐だけが残る**。

### 統合時の問題（私が修正）
`ProofsLean.lean` に配線したところ、`writeParsedMslMsrDestination?_facts` が
`WelcomeSpecialShape` と重複して環境エラー。新モジュール側を
`floatMAU_writeParsedMslMsrDestination_facts` に改名して解消（877 jobs）。

### 残り
`WelcomePEFloatMAUHalfCycleCopy` — `.h` の4分岐。`lowerParsedHalfMultiply/Add/Fma/Passa` の
ソース形状反転が必要。

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド41: float MAU 行形状が**無条件で完成**

独立検証: `lake build ProofsLean` → **878 jobs 成功**（`WelcomeHalfMAUCopy.lean` 696行を配線）。

### 証明
- `welcomePEFloatMAUHalfCycleCopy_holds`
- `welcomePEFloatMAUCycleCopy_holds`
- **`executeParsedFloatMAUsAtPE_zeroShape_static_unconditional`** — 完全な行形状
  （`Lm1WritesDoubleCopy ∨ Lm1WritesNarrow`）が仮定なしで成立

### 4つのソース形状反転
`welcomeHalfMAU_lowerHalfMultiply/Add/Fma/Passa_sources` — それぞれの lowering が
`parsedFloatMAUSourceAttrs?` 経由でしかソースを得ないことを証明。

### 閉じ方
1. `parsedFloatMAUSourceAttrs?` は `.memory` か `.forward` のみ
2. 零状態では `.memory` は `⟨0,0⟩`、`.forward` はポイズンで失敗
3. ゼロレーン上の half データパスは `⟨0,0⟩` を返す（フラグ組合せを `decide`）
4. 4分岐（lowering 失敗 / extend 拒否 / 読み出し失敗 / selector 両分岐）を網羅

残り: **なし**（この Prop について）。


## ラウンド41: 4整列の整除補題と `.l1bm` 行形状を証明

独立検証: `lake build ProofsLean` → **879 jobs 成功**（`WelcomeL1PEShape.lean` 665行を配線）。

### 1. 4整列の整除補題（ラウンド34から未解決だった穴）
`nat_mod_align`（`words ∣ capacity` の下で `(n / words * words) % capacity % words = 0`）、
`toDirectMemoryAccessMode_address_mod_four`、`toDirectMemoryDestination_address_mod_four`。
`.t` 分岐は `omega`、他は整除補題で閉じた。これが `l1ToPEWrites_doubleCopy` の前提そのもの。

### 2. `.l1bm` ブロードキャストの行形状（cycle / producer / stage レベル）
`executeParsedL1ToPEProducer_mem_lm1_shape` まで到達。零バスと4整列から
`Lm1WritesDoubleCopy ∨ Lm1WritesNarrow` を導出。

### 未証明
`WelcomePEL1ToPEShapeObligation`。理由は2つ:
1. 行の `.lm1` writer が**別の行**であり得る（broadcast が `.mem lm0`/`.bar`/`.nowrite` のみの場合）
2. broadcast が writer の場合、`.lm1` 宛先を持たない行リストについての**整数段のリストレベル `.lm1` provenance** が未証明

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド42: 整数段 provenance は既に証明済みと判明、`.l1bm` 単一行インスタンスを証明

独立検証: `lake build ProofsLean` → **880 jobs 成功**（`WelcomeIntegerProvenance.lean` 701行を配線）。

### 私の brief の誤り
「整数段のリストレベル `.lm1` provenance が未証明」と書いたが、**ラウンド39で証明済み**だった
（`welcomePEIntegerStageLm1Provenance`、`WelcomeLm1Frame.lean:1573`）。エージェントは再証明せず、
消費者向けの形（`welcomeIntegerPrep_lm1_free` など）で述べ直した。

### 新規証明
- `welcomePEWriteShape_singleton_of_l1bmMemLm1` — **`.l1bm` ブロードキャストが writer の単一行インスタンス**
  （前ラウンドの残り2の後半）。段パイプラインを剥がし、整数段の外側フィルタが当該行を落とすことから合成
- `welcomePEWriteShape_of_l1bmWriter_of_integerOrInert` — 整数/不活性行を伴う複数行版
- `executeIntegerProducerInstructionLine_pe_conditions` — 成功した step から段剥がしの前提を導出（`WelcomePEUnrefuted` 不要）
- `l1bmBroadcast_parsedExpr_predicates` — ブロードキャスト行が他の producer 述語すべて偽であること

### 残り
1. 中間族 producer を伴う複数行（それらの段の write-list レベル `.lm1` provenance が未整備）
2. broadcast が writer でない行（8族分解）
3. `WelcomePEL1ToPEShapeObligation`

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド42: matrix MAU 行形状（narrow 半分は無条件）

独立検証: `lake build ProofsLean` → **881 jobs 成功**（`WelcomeMatrixMAUShape.lean` 1618行・46宣言を配線）。

### 無条件
- `executeParsedMatrixMAUProducer_zeroNarrow_static`（`.double` でない静的幅 → `Lm1WritesNarrow`）
- `executeParsedMatrixMAUProducer_widthCount` — **任意状態**で静的幅 + `.lm1` write 数 ≤ 4
- 数え上げは 1024² の総当たりではなく、指標和（`sum_map_indicator`、`allMABCoordinates_indicator_sum`）で処理

### 条件付き
`WelcomePEMatrixMAUZeroBus`（零状態で matrix-MAU バスの下位半分が 0）を仮定すれば完全な形状。
この Prop は
`parsedMatrixMAUCalculateRows_zero_store`（零ストア + 零アキュムレータ → 零行）と
packing 段（`parsedMatrixMAUPackPEBus?` の零レーン）に還元済み。
層となる補題（`matrixBlockFloatDot_zero_left`、`encodeMAUValue_zero`、`parsedMatrixMAUProductRow_zero_store`、
`readParsedMatrixMAUSourceAtMAB_zero` など）は既に証明されている。

### 未着手の技術的障害
`parsedMatrixMAUCalculateRows?` の `do` ブロックの `cases precision` 再述。
`match precision with …` が**依存マッチ**に精緻化され、汎用行ステップが構文的に書き換わらないため。

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド43（中間）: 6族 Props は行形状からは落ちない

エージェントの中間報告:
**family 仮定は「その族の行が唯一の `.lm1` writer」を含意しない**。
例: `.matrixWrite`/float-MAU/matrix-read/L1BM の行が PE バンクを書かず、
plain `.alu` 行が `lm1` を書く構図が合法（`welcomeLm1Writer_unique` は2人の writer しか禁じない）。
`.matrixWrite` と `.l2bm` は**常に**非 writer。

さらに「族の行が writer」の場合でも、同行に任意の companion 行があると、
round-42 の残り（**段の write-list レベル `.lm1` provenance**）が必要（bank frame では不足）。

→ 方針転換: 行形状から族 Props を導くのではなく、
(a) float-MAU と matrix-MAU の writer 行について単一行/行レベル・インスタンスを新設、
(b) matrix-MAU 段形状を任意の現在状態へ一般化、
(c) 残りを正確なマップとして提示。


## ラウンド43: 6族 Props は「writer が別行」の構造で落ちないと確定。writer 側インスタンスを整備

独立検証: `lake build ProofsLean` → **882 jobs 成功**（`WelcomeFamilyInstances.lean` 688行を配線）。

### 決定的な構造
**どの family 仮定も「その族の行が唯一の `.lm1` writer」を含意しない。** 6族 Props は
writer が別行である線も量化する。`.matrixWrite` と `.l2bm` は**常に**非 writer。

### 証明された writer 側インスタンス
- `welcomePEWriteShape_singleton_of_floatMAU`（無条件）
- `welcomePEWriteShape_of_floatMAUWriter_of_inertCompanions`
- `welcomePEWriteShape_of_matrixMAUWriter_of_inertCompanions`（`ZeroBus` 条件付き）
- `welcomePEWriteShape_singleton_of_matrixMAU_of_zeroBus`
- 既存: `welcomePEWriteShape_of_matrixReadWriter`、`welcomePEWriteShape_of_l1bmWriter_of_integerOrInert`

### 次に必要なもの（構造的な要）
**「unique-writer dispatch」定理を1本**: 未反証行について、writer がいずれの行種別であっても
その行の形状から線形状が従うことを示す。middle-family companion がある場合は
**段ごとの write-list レベル `.lm1` provenance** が必要（bank frame では不足）。

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド43: `WelcomePEMatrixMAUZeroBus` を証明 — matrix MAU 形状が無条件化可能に

独立検証: `lake build ProofsLean` → **883 jobs 成功**（`WelcomeMatrixMAUZero.lean` 804行・17定理を配線、scratch 削除）。

### 証明
`welcomePEMatrixMAUZeroBus` — 零状態で matrix-MAU バスの下位半分が 0。
**4精度すべてを個別に**閉じた（`.d`/`.f`/`.g`/`.h`）。`.l`/`.i`/`.s` は `parsedMatrixMAUFloatFormat = none` で矛盾。

### 副産物の注意（エージェントが指摘）
`parsedMatrixMAUCalculateRows_zero_store` の無条件 `accLength` ガードは `mul`/`add`/`passa` には
**適用できない**（アキュムレータが `[]` で `lanesPerPE ≠ 0`）。実用形は `_of_fma` で、
非 fma は空虚なガード経由。記録済み。

### 証明の連鎖
行計算（精度別 + 汎用）→ 計算分解（kind 別）→ packing（`parsedMatrixMAUPEOutput_zero_low` で
非 round `.h` のみ下位半分が非零になり得るが rows 2,3 が 0）→ 主定理。

### 残り
**なし**（この Prop について）。下流の形状補題は `zeroBus` 引数を持つので、
`welcomePEMatrixMAUZeroBus` を渡して**無条件化**できる（次ラウンドで実施）。

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド44: matrix MAU 形状が無条件化、writer 5種が統一インターフェースに

独立検証: `lake build ProofsLean` → **884 jobs 成功**（`WelcomeMatrixMAUUnconditional.lean` 269行を配線）。

### 証明
- `WelcomePEMatrixMAUProducer_zeroShape_static` / `WelcomePEMatrixMAUAndWrites_zeroShape_static`（無条件）
- `welcomePEWriteShape_of_matrixMAUWriter_of_inertCompanions_unconditional`
- `welcomePEWriteShape_singleton_of_matrixMAU`

エージェントは条件版と無条件版の**文を機械的に diff** して 10/10 identical を確認（他の仮定は変えていない）。

### 統一インターフェース
plain / matrixRead / floatMAU / matrixMAU / l1bm の **5種の writer** が無条件で揃った
（行レベルと単一行の両方、存在するものは）。

### 残り
1. writer が別行（6族 Props が量化するケース）
2. middle-family companion の write-list レベル `.lm1` provenance
3. `WelcomePEMixedPlainInertFlagAgreement`

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド44: 中間5段の write-list レベル `.lm1` provenance を全証明（round-42 の穴を閉鎖）

独立検証: `lake build ProofsLean` → **885 jobs 成功**（`WelcomeStageProvenance.lean` 1874行を配線）。

### 証明（5段すべて）
`WelcomePEMslMsrStageLm1Provenance` / `WelcomePEFloatReluStageLm1Provenance` /
`WelcomePEBlockFloatStageLm1Provenance` / `WelcomePEL1ToPEStageLm1Provenance` /
`WelcomePEMatrixMAUStageLm1Provenance` + 束ね `welcomePEStageLm1ProvenanceForm`

形は「**PE0 の outgoing ファイルを commit し、かつ `.lm1` フリーな write list が存在する**」
（実行器はリストを返さないので存在形が正確）。

### 新しい base case
`writeParsedMslMsrDestination?_clean_commit` / `writeParsedL1ToPEDestination?_clean_commit`。
既存の bank レベル `..._lm1_of_ne` では「ゲートで抑止された `.lm1` 書き込み」を排除できないため、
書き込み自体を検査する強い形が必要だった。

### 残り
1. 行レベルの多族 companion 組み立て（clean リストと writer のリストの連結）
2. unique-writer dispatch
3. `WelcomePEL1ToPEShapeObligation`

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド45: `WelcomePEMixedPlainInertFlagAgreement` が**偽**と判明（反例を Lean で証明）

独立検証: `lake build ProofsLean` → **886 jobs 成功**（`WelcomeFlagAgreement.lean` 485行を配線）。

### 反証
`welcomePEMixedPlainInertFlagAgreement_false`。
反例は「`.zero` 行が lm1 を書き自己フラグは偽」+「`.noforward` 行が masked `.mem lm0` 宛先を持ち自己フラグは真」。
行フラグは真、plain 行のフラグは偽で一致しない。`Legal` の17フィールドも通る合法行。

### 重要: 反例は**形状の反例ではない**
同じ行で `WelcomePEWriteShape` と還元構造の本体が**成立**することを形式証明済み
（還元構造の本体は入力非依存で閉じる）。したがって反証が刺さるのは**中間命題だけ**。

### 帰結
1. `..._of_flagAgreement` 系は**仮定が充足不能**になり無効化
2. 実用できる集約は `welcomePELm1WriteShapeObligation_of_eight_and_inertFlagsClear` のみ
3. mixed クラスには「**自由フラグでの plain 行形状**」が必要
   （`plainRow_lm1_shape` が行フラグ固定のため）

### 未解決
還元構造 `WelcomePEMixedPlainInertStructureReduced` が一般に成立するかは未証明・未反証
（反例は入力非依存で通るため）。

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド45: **unique-writer dispatch を5種すべて証明**（要の完成）

独立検証: `lake build ProofsLean` → **887 jobs 成功**（`WelcomeWriterDispatch.lean` 1340行を配線）。

### dispatch 定理（5種）
`welcomePEWriteShape_of_plainWriter_dispatch` / `_matrixReadWriter_dispatch` /
`_floatMAUWriter_dispatch` / `_matrixMAUWriter_dispatch` / `_l1bmWriter_dispatch`

いずれも `(expressions) → WelcomePEWriteShape expressions` で、**`WelcomePEUnrefuted` 引数を取らない**
（行の条件は step 等式から読む）。整数段 writer は `intFree` も不要になった（文が強い）。

### unique-writer 系（5種）
`..._of_plainWriter_unique` ほか。freeness 束を
`rows : ∀ x ∈ line, x ≠ e → WelcomeRowHasNoLm1Destination x` に置き換えた形。

### 組み立て層
- `Lm1WritesShape` + `lm1WritesShape_append_free_split` + 6つの位置別系
- `executeIntegerProducerInstructionLine_pe_commit_split`（6段のリストを合成）
- `welcomePEWalkFilter_integer` / `_float`（per-PE walk のフィルタが行のフィルタと一致する橋）

### 新しい段事実
- `executeIntegerProducerLineAtPEs_zero_prepared_float` — 整数段 = prepared ++ float list（round-42 の穴）
- `executeParsedMatrixMAUAndWrites_shape_of_filter_singleton` — **任意の現在状態**での matrix-MAU 段形状

### 残り
1. `writeBanks` → 行ローカル `rows` の構文橋
2. float-MAU の **リストレベル** provenance（bank frame のみ存在）
3. `flagEq` / `notDouble` / `staticWidth` / companion の不活性性は仮定のまま

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド46: float-MAU のリストレベル provenance を証明、`floatEmpty` を除去

独立検証: `lake build ProofsLean` → **888 jobs 成功**（`WelcomeFloatProvenance.lean` 1048行を配線）。

### 証明
- `executeParsedFloatMAUsAtPE_clean_commit` — 段レベルの存在形（`.lm1` フリーな commit）
- `executeParsedFloatMAUsAtPE_lm1_frame_from_clean` — 既存の bank frame を導出（**強い**ことを確認）
- `executeIntegerProducerLineAtPECore_prepared_float_clean`（任意 pe）、
  `executeIntegerProducerLineAtPEs_zero_prepared_float_clean(_of_line)`（PE0 walk）
- `WelcomePEFloatMAUStageLm1Provenance`（6段目の provenance）

### 帰結
4つの dispatch 定理から `floatEmpty` を除去し、**行ローカルの `rows` 仮説**に置き換えた版
（`..._dispatch_floatRows` と `..._unique_of_floatRows`）を証明。
エージェントは scratch で「旧文が新文から導出できる」ことも確認し、緩めただけであることを検証済み。

### 残り
1. `writeBanks` → 行ローカル `rows` の構文橋（**最後の要**）
2. writer 形状の side condition（`flagEq`/`notDouble`/`nodup`/`staticWidth`）は仮定のまま

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド46: 構文橋を証明、行レベル集約と7分類を完成。**残る主ブロッカーは「slot 依存の行形状」**

独立検証: `lake build ProofsLean` → **889 jobs 成功**（`WelcomeFinalShape.lean` 929行を配線）。

### 証明
- **`welcomeLm1Writer_rows`**（構文橋）— `welcomeLm1Writer_unique` + `writeBanks_eq_bankList` + `Expr.id`
  から、唯一の `.lm1` writer だけが `.lm1` 宛先を持つことを導出
- 5種の writer 行定理（plain / matrixRead / floatMAU / matrixMAU / l1bm）
- `welcomePEWriteShape_of_lineData`（行レベル集約）
- `welcomePELm1LineDispatchData_of_components`（writer の**7分類を網羅**）

### 条件付き最終定理
`welcomePELm1WriteShapeObligation_of_dispatch` / `welcomeLowerBound_two_of_dispatch` /
`welcomeAnswer_optimal_of_dispatch` — いずれも `WelcomePEDispatchResiduals` を仮定。

### 主ブロッカー (a): companion 分割が**制限**
5つのデータ束は整数段フィルタが `noforward*/wait* ++ e ++ noforward*/wait*` であることを要求する。
**理由**: `plainRow_lm1_shape` / `matrixReadRow_lm1_shape` が**初期スロット**で述べられているため、
writer より前に準備する行があるとスロットが変わる。例 `[matrixRead (no lm1 dest), alu → lm1]` は
合法かつ未反証だが還元の外。閉じるには**スロット非依存の行形状**が必要で、旧 family Props にも影響する。

### その他の残り
(b) 中間フィルタの単一形、(c) マスクフラグ（偽なので入力非依存で吸収）、
(d) `WelcomePELm1PhantomWriterProvenance`、(e) `WelcomePESpecialALUWriterShapeObligation`

→ `LowerBound 2` / `Optimal` は**無条件には存在しない**。


## ラウンド47: 主ブロッカー (a) を plain / matrixRead について閉鎖

独立検証: `lake build ProofsLean` → **890 jobs 成功**（`WelcomeSlotFree.lean` 1275行を配線）。

### 構造的発見（brief の想定より強い）
`prepareParsedIntegerMatrixReadLineExpressions` は行リスト全体を通じて
`files` と `oldSlots` を**固定**し、`nextSlots` だけを渡す。したがって先行する準備行は
writer の**初期出力スロット**しか変えない。→ `.double` のコピー事実も narrow の数え上げも
**任意の先行行に対して成立**する。brief で提案した narrow/double 分割は不要だった。

### 証明
- `plainRow_lm1_shape_of_startSlots` / `matrixReadRow_lm1_shape_of_startSlots`（任意スロット）
- **`welcomeIntegerPrep_split`** — 整数段を任意位置で分割（`welcomeIntegerPrep_single_writer` を置換）
- `welcomePEWriteShape_of_plainWriter_arbitrary` / `_matrixReadWriter_arbitrary`（任意の before/after）
- `WelcomePEPlainWriterDataForSlotFree` / `WelcomePEMatrixReadWriterDataForSlotFree` — `noforward*/wait*` 分割が消えた
- `welcomePELm1WriteShapeObligation_of_dispatchSlotFree`

保守性も確認: `..._slotFree_of_companion` で旧パッケージが新パッケージを含意することを証明。

### 残り
1. `flagEq` は plain パッケージに残る（companion が masked 宛先を持つ場合）
2. floatMAU / matrixMAU / l1bm / specialALU / phantom は round-46 のパッケージのまま
3. `LowerBound 2` / `Optimal` は未主張

→ 条件付きの `WelcomePELm1WriteShapeObligation` まで到達。


## ラウンド47: 残存義務 (d) を証明、特殊 ALU (e) は `.h` block-float のみに縮小

独立検証: `lake build ProofsLean` → **891 jobs 成功**（`WelcomeResiduals.lean` 1662行を配線）。

### (d) 証明
`welcomePELm1PhantomWriterProvenance` — phantom 行（`.noforward`、未完了 `.wait`、共有 `.l1bm`、
`.matrixWrite`、`.l2bm`）と writer 無しの場合。
`noforward`/`wait` で精密化した整数段 provenance と、float-MAU のリストレベル provenance を合成。

### (e) 縮小
- `welcomePEMslMsrWriterShapeObligation`（無条件）+ **`welcomePEMslMsrExecutorExposure`**（以前の残存名も解消）
- `welcomePEFloatReluWriterShapeObligation`（無条件）
- `welcomePEBlockFloatLowPrecisionWriterShapeObligation`（`.d/.f/.g`、無条件）
- `welcomePESpecialALUWriterShapeObligation_of_block`

### 残る唯一の形状事実
`WelcomePEBlockFloatNonLowWriterShapeObligation` — **`.h`（半精度）block-float writer**。
`parsedBlockFloatMab .h` の3語目が任意バスでコピーになることは反証済みなので、
行レベルで「4入力バスが零状態でコピーになる」読み出し解析が必要
（`welcomePEBlockFloatHalfZeroInputCopy` は全ゼロバスのみカバー）。

### その他
`flagEq`（masked companion）と最終組み立てが残る。`LowerBound 2` / `Optimal` は未主張。


## ラウンド48: plain 行形状が**フラグ非依存**に（`flagEq` を除去）

独立検証: `lake build ProofsLean` → **892 jobs 成功**（`WelcomeFlagFreePlain.lean` 2627行を配線）。

### 発見（brief より強い）
plain 行形状は**任意のマスクフラグ**で成立する。フラグは `resolveMemoryWriteSelection?`/
`resolveOmrWriteSelection?` 経由で「どの selection が prepared write に運ばれるか」だけを変え、
**宛先・データ・`.lm1` write 数には影響しない**。したがって `WelcomePlainStep.lean` の
28宣言の per-cycle 連鎖を `hsm : Bool` 自由で再証明すれば十分だった。異なるサブケースは無い。

### 証明
- `plainRow_lm1_shape_of_startSlots_anyFlag` / `..._linePrep_anyFlag` / `..._trueFlag` / `..._rowFlagFalse`
- `welcomePEWriteShape_of_plainWriter_arbitrary_flagFree`（`flagEq` を削除）
- `WelcomePEPlainWriterDataForFlagFree` と dispatch 一式
- `welcomePELm1WriteShapeObligation_of_dispatchFlagFree`

保守性: `..._flagFree_of_slotFree` / `..._of_companion` で旧パッケージが新パッケージを含意。
round-45 の反例が新パッケージを満たすことも確認済み。

### 残り
1. `WelcomePEPlainImmediateDoubleObligation`（`notDouble`）— immediate + `.lm1 .double` の入力非依存性
2. 他5種の dispatch と `WelcomePESpecialALUWriterShapeObligation`

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド48: `.h` block-float writer を証明 → 特殊 ALU writer 義務も無条件に

独立検証: `lake build ProofsLean` → **893 jobs 成功**（`WelcomeHalfBlockFloat.lean` 967行を配線）。

### 証明
- `welcomePEBlockFloatNonLowWriterShapeObligation`（`.h` 半精度）
- 系: **`welcomePEBlockFloatWriterShapeObligation`**（低精度 + `.h`）
- 系: **`welcomePESpecialALUWriterShapeObligation`**（msl/msr + float-relu + block-float）

**特殊 ALU writer の義務が無条件になりました。**

### 閉じ方
- `parsedBlockFloatMab_h_eq_half` + `halfBlockFloatMab_word_two_copy`:
  16bit レーンが `< 512` か `= 32768` なら `maxExponent = 0` 分岐に入り、出力は 0 か 32768、3語目はコピー
- 零状態の読み出し解析: `.fixed` は座標 `⟨0,0,0,0⟩` で 0/1/2/3/32768、`.memory` はゼロ、`.forward` は失敗
- 「実際に読まれたバスのみコピー」を持つ fold 変種

残り: **`flagEq`（既に `WelcomeFlagFreePlain` で解消済み）の配線**と最終組み立てのみ。

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド49: 最終組み立てを実施。`matrixMAU` パッケージを無条件化、残りは4つのデータパッケージ

独立検証: `lake build ProofsLean` → **894 jobs 成功**（`WelcomeAssemblyFinal.lean` 450行を配線）。

### 無条件になったもの
- `welcomePELm1PhantomWriterProvenance`（既存）
- `welcomePESpecialALUWriterShapeObligation`（既存）
- **`welcomePEMatrixMAUWriterData`（新規）** — `groupsUnique` から「受理行は同じ issue group の2行を持てない」
  → `.mau` 行は高々1つ → matrixMAU フィルタは `[e]`、floatMAU フィルタは `[]`
  （系 `welcomePEWriteShape_of_matrixMAUWriter` も無条件）

### 条件付き（4つのデータパッケージ）
`WelcomePEPlainWriterDataFlagFree` / `WelcomePEMatrixReadWriterDataSlotFree` /
`WelcomePEFloatMAUWriterData` / `WelcomePEL1BMWriterData`

→ `welcomePELm1WriteShapeObligation_of_writerKindData`、
`welcomeLowerBound_two_of_writerKindData`、`welcomeAnswer_optimal_of_writerKindData`

### brief の訂正（エージェントが指摘）
**plain の「行形状」は無条件だが「データパッケージ」は無条件ではない。**
パッケージは float-MAU 行の不在と `notDouble ∨ 入力非依存` も要求する。
同様に matrixRead / l1bm パッケージも floatMAU フィルタ空を要求する。
→ **plain writer + float-MAU companion** の行はどの選言でもカバーされない。

### 各パッケージが開いている理由
1. float-MAU companion: float 行は group `.mauCalc`、plain/read/l1bm writer は `.alu`/`.mauRead`/`.l1bm` なので
   `groupsUnique` は共存を許す。現行の行形状が `floatFilter = []` を要求しているため
   （導出可能な `.lm1` フリー性では足りない）
2. plain の `notDouble`: `welcomePEPlainImmediateDoubleObligation` は全 plain 行のみ
3. floatMAU: 整数段の全行が `.noforward` であることを要求
4. l1bm: `filter l1ToPE = [e]` を要求

→ `LowerBound 2` / `Optimal` は**条件付き**。


## ラウンド50: float-MAU companion 制限を**除去**（plain / matrixRead / l1bm）

独立検証: `lake build ProofsLean` → **895 jobs 成功**（`WelcomeFloatCompanion.lean` 985行を配線）。

### 結果
3種のパッケージから `filter floatMAU = []` を**完全に除去**。しかも弱めたのではなく、
**導出可能**であることを証明（`welcomeLm1Writer_rows` + 「writer は float producer でない」→
`floatFilter_lm1Free_of_rows`）。両方向の含意を証明済み。

- `WelcomePEPlainWriterDataForNoFloat` / `WelcomePEMatrixReadWriterDataForNoFloat` / `WelcomePEL1BMWriterDataForNoFloat`
- 新しい行形状: `welcomePEWriteShape_of_floatRows_intShape`、
  `..._of_plainWriter_arbitrary_floatRows`、`..._of_matrixReadWriter_arbitrary_floatRows`
- 組み立て: `welcomePELm1WriteShapeObligation_of_writerKindDataNoFloat`
- **回帰なし**: `..._of_old` で旧4パッケージからも同じ義務が出ることを確認

### 残り（条件付きのまま）
1. `WelcomePEFloatMAUWriterData` — singleton float フィルタ + 整数段全行 `.noforward`（不変）
2. plain の `notDouble ∨ 入力非依存`
3. matrixRead の split/source/静的幅
4. l1bm の lowering + singleton L1 フィルタ

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド50: float-MAU パッケージが**無条件**に。L1BM パッケージは**反証**され、真の義務が判明

独立検証: `lake build ProofsLean` → **896 jobs 成功**（`WelcomeWriterPackages.lean` 1209行を配線）。

### 1. float-MAU パッケージ: 無条件化
`welcomePEFloatMAUWriterData_intRows` を**仮定なし**で証明。
singleton は `groupsUnique` + `.mauCalc` から、整数段 `.lm1` フリー性は writer 一意性から。
系 `welcomePEWriteShape_of_floatMAUWriter` も無条件。
技術的な鍵は「float 行形状を零・現在ファイルから**任意の現在ファイル**へ一般化」（読むファイルは零のまま）。

### 2. L1BM パッケージ: **反証**
- `l1ToPESecondRow_oldPackage_false`: 2つの `.l1bm` 行（turnaround フラグが異なる）は合法・受理・未反証
  → **round-49 のパッケージは偽**（未証明ではなく偽）
- `l1ToPETwoDestination_weakPackage_false`: 2つの `.mem` 宛先を持つ broadcast writer も合法
  → weak 版も偽

### 3. 負の結果（重要）
`welcomePEWriterKindDataResiduals_false` / `...Three_false` — **round-49 の4パッケージ束も新しい3パッケージ束も反証可能**。
したがって条件付き連鎖は多宛先 L1BM writer に対して**空虚**。

### 4. 真の残存義務
`executeParsedL1ToPEProducer_mem_lm1_shape` の**多宛先一般化**
（現行証明は `writeDestinations_mem_singleton_resolves` を中心に組まれている）。

条件付き: `welcomePELm1WriteShapeObligation_of_plainReadL1`、`welcomeLowerBound_two_of_plainReadL1`、
`welcomeAnswer_optimal_of_plainReadL1`。

→ `LowerBound 2` / `Optimal` は未主張。


## ラウンド51: L1BM の障害を**完全に解消**（多宛先形状を証明、パッケージは定理に）

独立検証: `lake build ProofsLean` → **897 jobs 成功**（`WelcomeL1MultiDest.lean` 1467行を配線）。

### 行形状
`executeParsedL1ToPEProducer_lm1_shape_atMostOne` — **任意の宛先リスト**で、
`.mem .lm1` 宛先が高々1つなら形状成立。
`writeCycles` → `AtPEs`（4096-PE walk）→ producer → stage の完全な連鎖。
宛先ループは新しい append 法則と `..._lm1_split_run` で除去。

### **「高々1つ」は仮定ではなく定理**
`writesUnique` が各行の `writeBanks` に `Nodup` を要求するため、合法行は `.mem .lm1` 宛先を高々1つ持つ
（`filter_isLm1_le_one_of_accepted`）。よって
`welcomePEL1BMWriterDataMultiDest_holds` を**仮定なし**で証明。

### 重要な負の結果
lowering の存在も要求すると**偽**になる（`l1ToPEMemorySource_withLowering_false`:
メモリ源の `.pbcast` は受理されるが `lowerParsedL1ToPE? = none`）。
dispatch は lowering で場合分けし、失敗枝を stage の成功と矛盾させて閉じる。

### 非空性
`welcomePEL1BMWriterDataForMultiDest_witness_strict` — round-50 の両パッケージを反証した
2宛先 witness が新パッケージを満たす。**旧パッケージが失った行を正確にカバー**。

### 組み立て（残り2パッケージのみ）
`welcomePELm1WriteShapeObligation_of_plainReadL1MultiDest (plain) (read)`、
`welcomeLowerBound_two_of_plainReadL1MultiDest`、`welcomeAnswer_optimal_of_plainReadL1MultiDest`

→ 残るは `WelcomePEPlainWriterDataFlagFree` と `WelcomePEMatrixReadWriterDataSlotFree` の2つ。


## ラウンド51: plain と matrixRead パッケージも**定理**に

独立検証: `lake build ProofsLean` → **898 jobs 成功**（`WelcomePlainReadPackages.lean` 1166行を配線）。

### plain
- `welcomePE_plainConstantWriter_inputIndependent` — companion 任意（`.noforward`/`.wait` 制限なし、
  `intOrInert` 不要）で入力非依存を証明。鍵は `welcomePlain_constantRow_writes_nextSlots`
  （定数行の書き込みが incoming/outgoing 両スロットに依存しない）
- `welcomePEPlainWriterDataDoubleFree` を**無条件**で証明
- `welcomePEWriteShape_of_plainWriter_closed` は**パッケージ不要**

### matrixRead
- `toDirectMatrixReadAccesses?_op_sources` — lowering から `op`/`sources` を逆算
- 静的幅は `lm1StaticWidth e` で仮定不要
- `welcomePEWriteShape_of_matrixReadWriter_closed` は**パッケージ不要**

### 残り
round-50 の `WelcomePEL1BMWriterDataNoSingleton` は round-51 の
`welcomePEL1BMWriterDataMultiDest_holds`（無条件）で置き換え済み。
→ 最終組み立てエージェントが全ケースを合成中。


## ラウンド51: **`Optimal welcomeSealedMachine welcomeSpec welcomeAnswer` を無条件で証明**

独立検証: `lake build ProofsLean` → **899 jobs 成功**（`WelcomeOptimalFinal.lean` を配線）。
`#check` で3定理の型を確認:
```
welcomeLowerBound_two : LowerBound welcomeSealedMachine welcomeSpec 2
welcomeAnswer_optimal : Optimal welcomeSealedMachine welcomeSpec welcomeAnswer
welcomePELm1WriteShapeObligation : WelcomePELm1WriteShapeObligation
```

### 7分類の全枝が定理で埋まった
| writer | 根拠 |
|---|---|
| plain | `welcomePEWriteShape_of_plainWriter_closed`（パッケージ不要） |
| matrixRead | `..._matrixReadWriter_closed`（パッケージ不要） |
| matrixMAU | `welcomePEWriteShape_of_matrixMAUWriter` |
| floatMAU | `welcomePEWriteShape_of_floatMAUWriter` |
| matrixWrite / l2bm / 不活性 / writer無し | phantom provenance |
| l1bm | 多宛先版（`welcomePEL1BMWriterDataForMultiDest_holds` は定理） |
| 特殊 ALU | `welcomePESpecialALUWriterShapeObligation` |
| 未対応 ALU | `WelcomePEUnrefuted` で排除 |

### 正確な位置づけ（重要）
対象は **`welcomeSealedMachine`**（`State`、`step := executeNormalizedLine` で非 `.ok` を `none`）。
issue/アドレスモード/PEハザード/ブロックハザードの検査は**封印**されている。
したがって「**hazard-aware な `wholeMachine` 上の `Optimal`**」はまだでない。

### 残る作業
1. ハザード層（`HazardAwareState`）への持ち上げ — `seal` と検査の合成
2. `check.py` の証拠再生成（catalog の期待値 966/57）
3. `audit.json` の Welcome を `proven` に（生成カタログなので catalog 経由）


## ラウンド52: **`Optimal welcomeWholeMachine welcomeWholeSpec welcomeAnswer` を証明** — Phase 4 の数学的内容が完成

独立検証: `lake build ProofsLean` → **900 jobs 成功**。
```
#check welcomeWholeMachine_optimal : Optimal welcomeWholeMachine welcomeWholeSpec welcomeAnswer
#check welcomeWhole_partialOptimal : PartialOptimal wholeMachine welcomeWholePartialSpec welcomeAnswer
#print axioms welcomeWholeMachine_optimal → [propext, Classical.choice, Quot.sound]
```

### 2層で提供
- **(A) `PartialMachine` 語彙**（`wholeMachine` を直接）: `welcomeWhole_partialCorrect/LowerBound/Optimal`
- **(B) `ProofsLean.Optimal` 語彙**（`wholeMachine` の total presentation）: `welcomeWholeMachine_optimal`

literal な `Optimal wholeMachine` は**型が付かない**（`Optimal` は `Machine` 上に定義され、`wholeMachine` は `PartialMachine`）。
`wholeMachine.seal` は `Complete` が偽なので不可 — `wholeMachine_not_complete` で証明済み
（初期状態で pending な wait タグは `.unknown`）。

### 射影補題
`executeHazardAwareNormalizedLine_ok_project`: hazard-aware step の成功は `state.machine` 上の
`executeNormalizedLine` の成功に射影される。`noWait` は**本質的**（wait タグがあると wrapper は
`machine` 上で MV 完了を先に行う）で、Welcome 行では `welcome_noWait` で、初期状態からは全行で
`completePendingMvTagAll_welcomeInitialState` により解消。

### 値の一致
`welcomeWholeAnswer_values`: hazard-aware 実行と sealed 実行が `state.machine` で一致。

### 残る作業（管理上のゲート）
1. literal な `Optimal wholeMachine` が欲しければ `Optimality.lean` に ~10 行の再輸出が必要
2. `check.py` の証拠再生成（catalog の期待値 984/57 vs 実コーパス 966/57）
3. `audit.json` の Welcome を `proven` に（生成カタログ経由）


## ラウンド53: check.py の連鎖修復を試行（未完了）

### 修復したもの
1. `catalog.py` のコーパス総語数期待値を更新（984/57 → 966/57）。
   根拠: `git show HEAD:.../answer-encoding/reference.json` との差分が **4解答のみ**
   （problems/34: 7→6、35/36: 12→6、fizzbuzz: 98→93）で、いずれも解答の短縮。
2. `evidence/answer-encoding`、`evidence/parser-gap-audit`、`evidence/opcode-arity`、
   `evidence/raw-candidate-assembler` を再生成。

### 残っている陳腐化（19件の記録、うち**生きた証拠は2件**）
- `evidence/forwarding/reference.json` — `ProofsLean/Forwarding.lean` のハッシュが古い
  （コミット 6b49186「Model absent L1-to-PE forwarding as retained state」以降の変更）
- `evidence/lbf-encoded/reference.json` — 同上

残り17件は `forwarding/matrix-retention-assumption/` や `untyped-alu/initial-manual-assumption/` などの
**凍結アーカイブ**で、過去の誤ったモデルのコードハッシュを意図的に保存している。再生成してはいけない。

### 次に必要なこと
`check_forwarding_reference.py` と `check_lbf_encoded_reference.py` を再実行
（公式エミュレータが必要、42 + 11 ケース）。その後 `catalog.py` → `check.py`。

→ 数学的成果（`Optimal welcomeWholeMachine`）は完了しているが、リポジトリの受け入れゲート
（`check.py`）は未通過。


## ラウンド54: check.py の連鎖は「意味論的な未解決差分」で停止（管理ゲートは未通過）

### 試行と結果
`check_forwarding_reference.py` を再実行 → **失敗**:
```
{"index": 40, "unit": "lbf", "scenario": "disabled-narrow-off", "observed": "assembler_failure", "matched": false}
{"index": 41, "unit": "lbf", "scenario": "disabled-chain",       "observed": "assembler_failure", "matched": false}
forwarding abstraction has unresolved reference mismatches
```
LBF の2ケースが現在のモデルでは `assembler_failure` になり、記録済み期待値と一致しない。
これは README が記録している「L1BM の5ケースは未解決」と同じ種類の**意味論的差分**で、
証拠の再生成では解消しない。

**生成に失敗した証拠は破棄**（`git checkout -- evidence/forwarding/reference.json vectors.tsv`）。
壊れた記録を残さない。

### 受け入れゲートの現状
- `check.py` は **未通過**
- 直接の原因: `evidence/forwarding/reference.json` と `evidence/lbf-encoded/reference.json` の
  コードハッシュ陳腐化。ただし再生成すると意味論的な未解決差分が現れるため、
  **先に forwarding/LBF の意味論を決着させる必要がある**
- 数学的成果とは独立

## 他問題への展開: 零入力の罠（1.a-b で判明、カーネル検証済み）

Welcome の write-shape 義務は**零入力**で述べられている。1.a-b ではこの入力が使えない。

- `abEmpty_correct_at_zero`: 零入力での A−B の目標は `0` で、初期 LM1 も `0`。よって**空プログラムが既に正しい**。
  零入力の事実からは何も反駁できない。
- `abTarget_five_eq_zero`: 入力非依存の選言は零入力と all-five 入力（A=5,B=0）を比べるが、
  モデルは `5*1.0-0` を 0 にフラッシュするので両方 0。この選言でも反駁できない。
- float `.f` MAU のバスは `⟨output, 0⟩` なので、`.double` 書き込みは語 0,1 が 0、語 2,3 が計算値。
  零入力での `IsWelcomeCopy` は**空虚**で、`.double` 枝は家族ごとのデータ議論が要る。

**したがって他問題の下限証明の型は:**
1. 目標値が初期メモリと異なる**証人入力**を選ぶ
2. **状態一般の宛先解析**（分岐選択は式・制御・フラグ・maskRegisters のみに依存し、メモリデータに依存しない）
   で narrow 形状を導く
3. 家族ごとの `.double` データ議論をその入力で行う

1.a-b の成果: `abSealedMachine`/`abSpec`/`abInitialState`、1行反駁の大部分、`abLowerBound_two_iff_residual`
（残りは「`AbPEUnrefuted` の反駁」に正確に還元）、`ab_not_correct_of_narrowAtOnes`。
警告: post は bit-exact なので公式の 1e-4 許容より**強い**。反駁の差は ≥1.0 だが許容緩和は未形式化。

## モデル整合性の警告（mul7 プローブ、未解決）

`SingleFMA` モデルと公式エミュレータが **ALU forward (`$aluf`) と OMR マスクの相互作用**で食い違う。

- 素直な `fvmul $lm0v $t $ln0v` は X=5 で 0 を返す（subnormal FTZ）
- しかし公開6行解答は 35（正しい）を返す
- `smax $lm0v $aluf $nowrite; fvfma $aluf $ls64v $lr0v $ln0v` は入力非依存の
  `0x4241999A4241999A` を返す

→ **リポジトリのオペランド役割の読み方が誤っている可能性**。`$aluf` をソースとして読む箇所と
OMR マスクの解釈を、エミュレータのプローブで決着させる必要がある。

**影響範囲**: `SingleFMA` に依存する全下限証明（mul7、float 系）は、この整合が取れるまで
「モデル上の定理」であって実機の定理ではない。整数 ALU のみの問題（a-plus-b、plus-two）は
この経路を使わないため影響しない見込みだが、確認は必要。

**記録上の注意**: 「エミュレータは FTZ する」とも「subnormal を扱う」とも決めつけない。
ALU forward / OMR マスクの解決が先。

## 並列トラックの割当（調査結果に基づく）

調査 (`research/problems-survey.md`) の結論:
- challenge 25問、`wc -l` 合計 348、568 命令、91 ニーモニック
- 24/25 のスコアが記録 Top と一致（fizzbuzz のみ 93 vs 98）
- 出力バンク: 21 が LM1、3 が LM0、3 が DRAM
- Welcome 連鎖: 7 が汎用核（9,096行/17.4%）、36 が移植可能（38,967行/74.6%）、6 が専用（4,195行/8.0%）

難度順の推奨: plus-one(済) → **a-plus-b** → **plus-two** → 5.abs → 24.log2 → 8.fle → **convert-endian** → 13.mod3 → …

**FTZ の警告が暫定的に及ぶ問題**: `5.abs`, `24.log2`, `13.mod3`, `23.fizzbuzz-pe`（整数を f32 として扱う）。
`3.a-plus-b` と `2.plus-two` は純粋な整数 ALU なので影響しない。

稼働トラック（同時実行上限 8 のため順次投入）:
1. a-plus-b 下限
2. plus-two 下限
3. convert-endian 下限
4. 1.a-b の状態一般宛先補題
5. モデル整合性（`$aluf`/OMR とエミュレータ）
6. FizzBuzz 52語
7. 1.a-b 最短解探索
8. （待機）汎用核の抽出、（待機）独立監査

## 解答のテストケース過適合（重大、2.plus-two で確認）

`problems/challenge/2.plus-two/answer.vsm` は **5語で ACCEPTED** だが、
`idec`/`ixor` を公式テストケースの入力値に合わせた命令列で、**全入力で正しくない**。
全ゼロ入力で公式 judge に掛けると 0/20 正解、全出力が `0xffffffff`（正解は 2）。

`mncompile/PLAN.md` §10 と README が既にこれを記録し、汎用の7行解
（`imm ui"0x00000002" $s449/1000; nop; ladd ...`）を示している。資源下限は 6（証明ではない）。

**プロジェクトへの影響:**
- 「最短 Accepted」は**テストケース基準**であり、仕様（全入力で正しい）基準ではない
- 24/25 が記録 Top と一致という調査結果も、Top がテストケース基準である以上、
  仕様上の最短性を意味しない
- 要件「入力の全許容範囲について正しさを証明する」を満たすには、
  各解答が**普遍的に正しいか**を先に監査する必要がある

**TODO（全25問）**: 各 answer.vsm を摂動入力（全ゼロ、全0xff など）で公式 judge に掛け、
普遍性を判定する。過適合があれば「普遍解の探索」が先に必要になる。

## FizzBuzz 52語トラック: 打ち切り（受理 <93 は得られず、資産は残した）

`research/experiments/fb52/STATUS.md` に全記録。再現可能な測定済み部品:

| 部品 | 実測コスト | 検証 |
|---|---|---|
| 8レーン位置/X (`prim_8lanes`, `val_x`) | 5 ALU (+1 imm) | `X=8b+p` ビット一致、1 `iadd` で8バイト書き込み |
| 8語→long語パック | 6 ALU (+1 imm) | 全サンプル PE で `ABCDEFGH` |
| d=4 逆算 (`val_inv`) | **4 ALU + 12 MAU** | `X,qf,r,jf,o,n` 全レーン生ビット一致、f32 `/79` が u≤28099 で正確 |
| 4桁抽出+パック+選択 (`val_digit`) | **18 ALU + 6 MAU** | 数値フィールド 25/25 バイト一致 |
| 統一ブロックモデル (`model.py`) | 32766B 検証 | 全セグメントで `n0 ≡ 10 mod 15`、prefix は仮想 d=1 の末尾 |

**未実装の阻害段**: 改行(o=d, ~3)、クラス/文字(~18-20、最大)、d=1/2/3 逆算補正(~12-16)、統合。

**修正後の予算**: 71 ALU + 28 MAU + 33 定数。定数 imm → 110語（93より悪化）、
定数 MAU ホスト → 77語投影、現実的 80〜85語。

**結論**: 62語の見積りは実測で崩れた。≤70 には桁段(18 ALU)と初期補正(12-16 ALU)の削減が必要。
不可能とは主張しない（検証した設計の実測床）。ベースライン 93 は再検証済みで ACCEPTED。

## 状態一般の宛先補題が完成（全問題の共通部品）

`ProofsLean/PlainALUDestination.lean`（問題非依存、machine/problem/input を一切含まない）:

```
prepareParsedIntegerALUExprCycle_destination_state_general :
  filesA.maskRegisters = filesB.maskRegisters →
  両方が成功 →
  writesA.map destination = writesB.map destination
```

仮定は **maskRegisters の一致と両実行の成功のみ**。分岐選択がメモリデータに依存しないことの形式化。
系 `prepareParsedIntegerALUCycles_destination_state_general` は4サイクル版。
副産物 `updateParsedIntegerALUForwardingCycle_ok_exists`（forwarding 更新は決して失敗しない）。

`ProofsLean/ABNarrowPlain.lean`: `abNarrowAtOnes_welcomeExpr` と
`abPE_singleWelcomeLine_not_correct_of_narrow` — `iinc` 1行の narrow 枝を end-to-end で閉じた。

**残る行レベルギャップ（全問題に共通）**:
1. 一般状態で実行器自身の write list を返す commit 補題（既存は存在形なので宛先を束縛できない）
2. plain 行での `prepareParsedIntegerMatrixReadLineCycles` と `prepareParsedIntegerALUExprCycles` の同定
3. その上で一般 plain-ALU 行の narrow 枝

**double 枝**は未着手。A=1.0,B=0 では float `.f` MAU の `.double` 書き込みは語0,1が0、語2,3が計算値なので、
家族ごとのデータ分割が必要（MAU: 2つの零語 / 整数ALU: A=0,B=1.0 でのコピー語）。
**許容差の注意**: `abSpec` の post は bit-exact で公式の 1e-4 より強い。下限は形式的には移行しない。

## 汎用核 `ProofsLean.MNCore.Generic` が完成（全問題の土台）

`ProofsLean/GenericLowerBound.lean`（1057行・98宣言）。`lake build ProofsLean.GenericLowerBound` → 890 jobs。

**主要 API**
- `sealedMachine Input` / `sealedProblem Input admissible initial post`
- `lowerBound_two_iff_rejects_unit_lines` / `_short_lines` / `_residual`
- `structure OneLineRefutation` + `lowerBound_two_of_oneLineRefutations`
- `.lm1` 代数（`Lm1FreeWrites` の append、6ブロック位置別系、filter 特徴づけ）
- hazard 持ち上げ: `hazardMachine` / `hazardExecute_project` /
  `hazardProblem_lowerBound_two_of_sealed_of_nil_pending`
- 証明書: `certificate_contains_short_line`（bound 2 では任意の証明書が全短行を含む）
- 値カーネル: `card_window_le` / `exists_uncovered_of_windows`

**検証**: `instantiate.lean` で AB と Welcome の既存 spec に対して型が通ること、
hazard 持ち上げが Welcome の下限を1行で再現することを確認。

**問題ごとに残る作業**（README §3）:
1. `Input`/`admissible`/`initial`/`post` を供給し空プログラムを反駁
2. 1行の分類（`.nop`/`.mv`/拒否 `.pe`/全 `.noforward` など）を反駁
3. 残差の値議論（`OneLineRefutation`）
4. 実行器リンク（write-shape 仮定を実行器から出す — stage commit/provenance は未汎用化）
5. hazard（初期状態の `pendingMv = []` と全タグ偽）
6. 出力形状が違う問題は独自の数え上げカーネル

**汎用化しなかったもの**: `IsWelcomeCopy`/`welcomeCopyMask`（マスク直書き）、
`WelcomePE{D,N}arrowShape`、`WelcomeStageCommit` の上位ラッパ、`WelcomeAssembly` の6リスト分割。

## 実行器リンクの解消（汎用核の項目4、問題非依存）

`ProofsLean/StageCommitSpecific.lean`:

```
executeIntegerProducerLineAtPECore_peRegisters_commit_list :
  実行成功 →
  ∃ (prepared) (floatWrites),
    prepareParsedIntegerMatrixReadLineCycles … (整数段のフィルタ) … = .ok prepared ∧
    next.peRegisters pe = commitParsedMaskedWrites (state.peRegisters pe) (prepared.1 ++ floatWrites)
```

**machine/problem/input/状態述語を含まない**。仮定は「step が成功した」だけ。
これで `GenericLowerBound` の残項目4（実行器の write list を名指しで得る）が解消。

副産物:
- `executeIntegerProducerLineAtPECore_peRegisters_commit_list_noforward`（float 無しなら存在形が消える）
- `parsedIntegerMatrixReadLineFourCycleStep_commit_eq`
- **`prepareParsedIntegerMatrixReadLineExpression_plain`**: plain 行では
  `prepareParsedIntegerMatrixReadLineExpression` が `prepareParsedIntegerALUExprCycles` + BAR 更新に
  **定義的に等しい**（証明作業は op 分割後の `rfl` のみ）

残り: 一般 plain-ALU 行の narrow 枝（4段の連鎖）と double 枝。

## A−B の正しい姿（探索結果）

- 問題は `problems/1.a-b`（MNIST, slug `mat_sub`）。`problems/challenge/1.a-b` は**存在しない**
- 現行解答は **3語**（`ACCEPTED!! score=3 j=3 m=0 bytes=77`）
- したがって最適性の目標は **`LowerBound 3`**（0/1/2語の反駁）。`LowerBound 2` は中間段

**探索が覆った範囲**（公式 assemble3 + emulator、`research/experiments/ab-search/`）:
- 1行の幅広テンプレート 787,576 生成、1/100 サンプルで 7,876 検査 → 2領域形は 0 個アセンブル
- 1行 2領域形 6,336 生成 → **0 アセンブル**（LM0 フィールド衝突など）
- 1行 pass 可能 2LW ライタ 520 → 253 アセンブル、**0 が 16/16 正解**
- 2行構造族 35,240 → 12,444 アセンブル、サンプル 424 中**最大 8/16**
- 公式ニアミス: 2語で 2048 正解 / 2048 不一致（ちょうど半分、予測どおり）

**ISA 事実**（公式ツールで確認）: 1ステップ1 LM0 アドレス、1命令1 LM1 宛先、MAU は 8 Float、
2LW の IALU 宛先は 16 = 8計算 + 8 pass-through（差分ではない）、mread は 8、MV は LM1 を書かない。

→ 1語目は差分を計算できず、2語目は高々8個。よって 3語が下限。
**未探索**: 787k 空間はサンプリングのみ、2行は構造族のみ（nop/wait パディングなし）、
タイムアウトは不可能の証明ではない、証明支援系による形式化はなし。

## 過適合監査の結果: 25問中 **1問のみ過適合**

`research/experiments/overfit-audit/REPORT.md`。300 実行（公式25 + 変種275）、289 受理 / 11 失敗。
失敗は全て `2.plus-two`。

**網羅的に検査した11問**: `1.plus-one`（全51値）、`2.plus-two`（全100値、全て誤り）、
`3.a-plus-b`（全10,201組）、`4.mul7`（全1001）、`5.abs`（全201）、`8.fle`（全2560）、
`13.mod3`（全256）、`23.fizzbuzz-pe`（全32,768 + シャッフル）、`24.log2`（全12）、
`16/20/21`（入力なしの単一インスタンス）。

**サンプリングした13問**: `6.fadd-mul`, `7.mul2`, `9.transpose-addr`, `10.gather-easy`,
`11.square-sum`, `12.convert-endian`, `14.mat-sq`, `15.contains`, `17.transpose-mab`,
`18.inversion-small`, `19.inversion`, `22.bit-reverse`, `25.hsv2rgb` — 6パターン + 構造的ケース。
「UNIVERSAL (sampled)」と分類（形式的証明ではない）。

**参照カーネル** `mncompile/benchmarks/challenge/*.py` が全25問の公式期待出力を再現することも確認。

**plus-two の反例**: 全ゼロ入力で全出力 `0xFFFFFFFF`（正解 2）。全100値でも 100/100 誤り。
解答に `x+2`/`ladd`/`linc` が無く、3つの `idec` と 2つの `ixor` が公式値に合わせた置換を行う。

→ 他の24問は記録解のまま下限証明を進めてよい。plus-two は普遍解への差し替えが必要。

## モデル監査の結論（先の警告を撤回）

`research/experiments/model-audit/REPORT.md`（587行、プローブ付き）。

1. **`$aluf` は問題ない** — 前ステップの ALU 2LW 出力。long-word 消費者は上位 long word を読む。
   ALU producer の無いステップでは無効化（"IALU is disabled"）。`Forwarding.advanceReference` と
   `ParsedIntegerInput.readWithForwarding` はこの挙動に一致。**BLOCKED.md の「パーサが誤読」は誤り。**
2. **OMR/$imr1 規則も一致** — 16bit エントリ = 4サイクル×4フラグ、既定 long マスクは上位 long word の4ハーフワード、
   書き込みエントリは**次ステップから**可視。Masks モジュールは全マッピングで一致。
3. **唯一の相違 D1**: Lean は post-ALU の `registers` を float MAU 段に渡すため、
   **同一行内で書いた OMR エントリを同じ行の masked MAU 書き込みが使う**。エミュレータは旧エントリを使う。
   宛先順序依存（`[$mem,$omr]` は旧、`[$omr,$mem]` は新）。mul7 では全 smax が mask 5 なので影響なし。
4. **`Mul7FloatGap` は誤診** — 解答は X を float として掛けていない。`smax` で X を `0x40E0XXXX` の下位16bitに詰め、
   `fvfma 0x40E0XXXX * 7.0f + (-42.0f) = 7 + 7X*2^-21` を作る。
   エミュレータは**FTZ**（aluf/OMR を排したプローブで確定）。`SingleFMA` は解答の FMA 値を正確に再現。
   **subnormal 対応を足してはいけない**（エミュレータと乖離する）。
5. **4.mul7 の解答は正しい**（ACCEPTED score 6）。ただし **spec の欠陥**: テストケースは X を各64bit要素の
   **奇数**32bit ワードに置くが、`Mul7Spec.lean` は**偶数**ワードに置き、`7X` の関係を主張している。
   定理は別の関係について述べられている。**書き直すか全単射を示す必要がある。**
6. **整数のみの問題は D1 の影響を受けない** — `3.a-plus-b`(6)、`2.plus-two`(5)、`12.convert-endian`(3)。
   convert-endian は `ConvertEndian.answerProgram` がエミュレータと完全一致（LM1 = 0xB33DEACB66DCE15F）。

→ 下限証明の機構（write-shape）は D1 の影響を受けない。mul7 の spec だけ修正が必要。

## 独立監査の結果（重要）

`research/experiments/audit/REPORT.md`（752行）。監査後、汎用核と AB/mul7 モジュールを
ルートに配線し直し、`lake build ProofsLean` → **909 jobs 成功**（従来の 900 は新モジュールを
型検査していなかった）。

### 1. Welcome の `Optimal` の**適用範囲**（重大）
- `#check welcomeWholeMachine_optimal : Optimal welcomeWholeMachine welcomeWholeSpec welcomeAnswer` は
  仮定なしで成立、axioms は標準3つ
- **しかし `welcomeSpec.admissible` は `toNat ≤ 50`**、post は **PE 0 のみ**を観測
- 公開の problem.md に 0..50 の制約は無い
- → **下限は公式問題に移行するが、正しさの半分は移行しない**。
  「公開 plus-one 問題の Optimal」は**未確立**。文書化済みの 0..50 / PE0 spec に対する結果
- 記録の訂正: `problems-survey.md` の「1.plus-one is done」はこの制限を繰り返していない

### 2. 汎用核は本物（確認）
- 再輸出は application であり restatement ではない
- `lowerBound_two_iff_residual` は `generic-core/instantiate.lean` でのみ使われ、実際の
  `outsideRefuted` を与えて iff を導く（下限ではない）
- hazard 持ち上げの4仮説はすべて使われる。ただし `tagsIncomplete` は**結論**には不要の可能性
  （completed-tag の完了は no-op で、core step は sealed step に射影する）

### 3. docstring の欠陥（要修正）
- `ABLowerBound.lean:49` が「all unconditional」と書くが `abShortLine_not_correct` は条件付き
- 同 :75-77/:736 が存在しない `ABNarrowTransfer` / `AbDoubleOrIndependent` / "section 12" を引用
- `Mul7LowerBound.lean:29` が存在しない `mul7_oneLine_not_correct` を名指し
- `Mul7Spec.lean:12` の「1024 words per PE」は 64倍の誤り

### 4. 健全性（確認）
- 全 `ProofsLean/*.lean` に本物の `sorry`/`admit`/`native_decide`/`axiom`/`opaque`/`unsafe` は**0**
- notes で「unconditional」と書かれた約60定理はすべて標準3公理のみ

### 5. 未追跡
項目2〜4 は未追跡ファイル。項目1 のみ commit 5565452 に含まれる。

## リソース事故: 公式 judge のクラッシュダンプで C ドライブ圧迫

WSL の `mncore2_emuenv` の `gpfn3_package_main` と `assemble3` が大量呼び出しで繰り返しクラッシュし、
1件約444MBのダンプを `%LOCALAPPDATA%\Temp\wsl-crashes` に生成していた（合計1.8GB）。
過適合監査の300回の judge 実行と探索の大量実行が原因。

**対処**: 診断用に最新2件を残して削除（1.8GB → 2.0MB）。

**再発防止の方針（全エージェントに適用）**:
1. 大量評価はリポジトリのネイティブシミュレータで行う（`tools/fbcheck.py` 等）
2. 公式 judge（`judge/judge-py/judge.py`）は最終確認のみ、問題あたり数回に制限
3. バッチ時はダンプディレクトリのサイズを監視し、200MB を超えたら停止して報告
4. judge 実行回数とシミュレータ実行回数を別々に報告させる

**注**: WSL のスワップ（約6GB）は稼働中で通常の使用量。クラッシュダンプとは別物。

## `2.plus-two`: 過適合の反証と普遍下限 5 への還元

`ProofsLean/PlusTwoLowerBound.lean`（628行、851 jobs、axioms 標準3つ）。

**普遍仕様**: `plusTwoSpec` は `∀ k, input k ≤ 99` → 出力 long k の低位語が `input k + 2`。
記録解は 5語（`plusTwoRecordedAnswer_score = 5`）。

**カーネル検証済みの反証部品**:
- `plusTwoLine1_perPE_value` — 全ゼロ入力での第1行の閉じた計算が出力 long 9 の低位語に `0xFFFFFFFF` を書く（`decide`、`native_decide` ではない）
- `plusTwoLine1_step_value` — 全機械の step に持ち上げ
- `plusTwoRecorded_not_correct_of_suffixFrame` / `plusTwoRecorded_not_optimal_of_suffixFrame`
  — 4行の接尾辞が語19を保存すれば `¬ Correct` / `¬ Optimal`

**普遍下限への還元**:
- `plusTwo_execute_coverage` — 各行が観測出力の高々4語を変えるなら `n` 行で高々 `4n`
- `plusTwoLowerBound_five_of_coverage` — `PlusTwoLineCoverage` から `LowerBound plusTwoSealedMachine plusTwoSpec 5`

**残る2つの Prop**（公理ではない）:
1. `PlusTwoSuffixPreservesWitness` — 4つの具体な plain-ALU 接尾辞行の状態一般 frame
2. `PlusTwoLineCoverage` — 任意の行が高々4観測出力語を変える（非 plain 族含む）

**普遍解**: `mncompile` の7行カーネルが公式・全ゼロ・全99・連続入力で Accepted（未形式化）。

**ビルド状況の訂正**: `StageCommitSpecific` は実際にはビルド成功（857 jobs）。
壊れているのは `AplusBLowerBound` のみ（`a-plus-b` 担当が作業中）。

## ラウンド170: 幅による反駁は `.double` で破綻、2つの plus-two 命題は**偽**

ルートビルド: 914 jobs 成功（`ABWidthBound`, `ValueProvenance`, `AplusBLowerBound` を配線）。

### 1. 幅の数え上げ: `.word`→4 / `.long`→8 / **`.double`→16**
`ProofsLean/ABWidthBound.lean`。`.double` 宛先は1式で16語書くため、幅<16の議論では反駁できない。
`four_mul_count_le_eight : 4·count ≤ 8 ↔ w ≠ .double`、鋭い上界は16。

使える閉路: `ab_not_correct_of_lm1WidthNotDouble` — **count ≤ 4 かつ静的幅 ≠ .double ⇒ 不正解**。
族ごとの count 上界は既存（`Lm1ChunkFacts`, `..._widthCount`, `l1ToPEWrites_length`,
中間段の `.lm1` フリー性）。

`.double` の残路（未形式化）: A=0,B=1.0（目標 `0xBF800000`）では初期語が 0 か `0x3F800000` のみ。
4つの4整列 `.double` 窓で16語を覆うと窓は 0,4,8,12 に固定され、アドレス 2,3,6,7,10,11,14,15 は
データ語2,3から書かれる → 8語が誤り。**汎用の初期読み出し値補題1本**で済む。

### 2. `2.plus-two` の2命題は偽
- `PlusTwoSuffixPreservesWitness` は偽: 宛先は式だけの関数ではなく
  `toDirectMemoryAccessMode?` が `bar1` に依存 → **状態に依存**。`destination_state_general` は
  `ParsedMaskExecutionControl`（bar0/bar1/tWord）を固定するので、零状態から任意状態への移送は**不健全**
- `PlusTwoLineCoverage` は偽: `.double` 宛先は1行で20観測語のうち8語を変える。
  「行あたり高々4語」は成り立たず `4n` の数え上げは無効
→ `LowerBound 5` の数え上げ経路は**撤回**。4行候補が存在しうる。

### 3. convert-endian: 1段値来歴を証明（問題非依存）
`ProofsLean/ValueProvenance.lean`: prepared write のデータ = 2読み出しの `evaluateParsedIntegerAlu`、
閉包の保存（`commitParsedMaskedWrites_lm1_closure`）、行レベルへの持ち上げ。
残り: `LinePreparedDataInClosure`（8分岐の帰納）、非 plain 族、目標除外の証明書、2行の場合。

### 4. `3.a-plus-b` は6行だった
解答は2行ではなく**6行**（score 6）。spec と6行の実行器代数、per-PE core 成功まで証明。
`aplusbAnswer_correct` は未証明（`ipassa` core、4096-PE walk、commit readback、6行合成）。
`LowerBound 2` は `AplusBPEUnrefuted` の反駁と等価。

### 5. `readWriteAgree` による別ルート
`LegalParsedLine.localReadWriteAgree` は受理行の LM0 読みと書きに同じ静的 Region を強制する。
A は 0..31、出力は 32..63 なので、出力を書く行は A を読めない（BAR/T は初期0）。
1行反駁の第2ルートとして記録。

## クラッシュダンプ第3波と plus-two の残差整理

- ダンプが再び 629MB（01:52 のタイムスタンプ、全て `gpfn3_package_main` signal 6）に増加。
  削除して 2.0MB に。実行中の judge プロセスは検出されず（バーストは終了済み）。誰が呼んだかは未特定。
- MNIST 監査担当はネイティブシミュレータのみで実行中（judge 呼び出しは本日7回のみ）

### plus-two の反証は**真である2つの Prop** に還元
```
PlusTwoSuffixPreservesWitnessOfBar1Zero : bar1 = 0 の状態で接尾辞は語19を保存
PlusTwoLine1PreservesBar1Zero          : 第1行は bar1 を保存
plusTwoRecorded_not_correct_of_bar1Frame : 両方から ¬ Correct
```
旧命題（偽）と違い、両方とも実行器について**真**。第1行が `bar1 = 0` を保つのは
`parsedIntegerALUBarUpdates` が `.mem` 宛先で `[]` になるため（ParsedIntegerStep.lean:5216-5223）。

### 残る1ステップ = 依存マッチの射影（全トラック共通）
`prepareParsedIntegerALUExprCycle` の `.alu` 枝は
`match hRequest : expression.op.executionRequest with …` で包まれ、`.dec`/`.i` ではこの scrutinee が
定義的に還元しない（`supportsIntegerAt` が `if (i == l || i == i || i == s) = true` として残る）。
`hRequest` が結果に出現するため `rw`/`simp only` は "motive is not type correct" で拒否。
`split` は精度/演算を抽象のまま残し、`Nat.div`/`Nat.mod`/`==` の正規化が `rfl` で閉じない。

→ 2つの継続案: (a) 具体的な `==` 条件を展開前に `decide` で片付ける、
(b) 分岐局所の `destination_of_direct` 補題（`executionRequest` を回避）+ 4行の lowering が `some` であること。
**この (a)/(b) は ALU 来歴担当に委任済み**で、成功すれば plus-two と A−B の両方が閉じる。

## `2.plus-two` 普遍最短 = **6語**（探索で確定）

`research/experiments/plustwo-search/`。`cand6.vsm` が公式 judge で `ACCEPTED score=6 j=6 m=0`。

```
imm i"2" $t
iadd $m[1,3,5,7]    $aluf $n[1,3,5,7]
iadd $m[9,11,13,15] $t    $n[9,11,13,15]
iadd $m[17,19,21,23] $t   $n[17,19,21,23]
iadd $m[25,27,29,31] $t   $n[25,27,29,31]
iadd $m[33,35,37,39] $t   $n[33,35,37,39]
```

入力 0..99 は上位語が 0 なので、各出力 Long の下位32bitだけを書けば上位は初期0のまま。

**検証**: 公式・全ゼロ・全9・昇順・降順・ランダム3種・packed 256（5,120値）・全4096PE で受理。
大規模 22,165 ベクトル（packed 443,300/443,300、broadcast 409,600/409,600）で不一致0。

**5語が不可能な論法**:
- 非2LW の ALU 演算は1語で高々4つの出力 Long を計算（MSB 1LW、LSB 1LW は source-1 の pass-through）
- 20出力には ≥5語必要 → 5語なら全語が「4つ計算」で、定数設定の語を置けない
- 任意の x に x+2 を作るには 2 が必要だが、初期メモリは0、固定オペランドは全PEで2にならない
  （`$msb1` は 0x8000000080000000、`$peid/$subpeid` は 0..3）、immediate は ALU オペランドにならず、
  `imm i"2"` は 32bit パターン 0x0000000200000002 で 64bit の 2 ではない
- 探索: 8,766 生成 / 6,670 アセンブル / 4,685 評価 / **受理 560、全て6語**。
  5語最良（`near5.vsm`）は 16/20 Long で不受理。ランダム 2,000 中 0 受理

**隙間**: 定義域はサンプリング（22,165ベクトル）、クラス網羅だがアドレス網羅ではない、
5語データのみ格子は 743/7,776 のサンプル、エミュレータのタイムアウト 1,973、
証明支援系による形式化はなし。

→ 下限の目標は `LowerBound 6`（5語以下の反駁）。上記の「幅 + 定数不在」論法が形式化の筋。

## MNIST 48問の過適合監査: 47/48 普遍、1問が境界過適合

`research/experiments/overfit-audit/MNIST.md`。

**過適合は1問**: `36.matmul-trb-pkg-lm-256-16-16`（score 6）。
宣言定義域は `0≤x≤512` だが公式テストケースの最大は A=511 / B=510。512 を入れると
`hbfn/9`（9bit ブロック浮動小数）+ `hmmul` の共有ブロック指数が1ビナード進み、小さい値の下位ビットが落ちる。
証人 `A[0,:]=[512,1,...,15]`, `B[0,:]=[0,...,15]` で期待 1240 に対し実際 **1248**。
公式 judge で確認済み（1回のみ、`pos=(0,0) actual=1248.0 expected=1240.0`）。
511 に変えると正確（1240）。

**精度限界（過適合ではない）2問**:
- `9.sumrow-mini` — 16項和が float32 で 15 ulp 超過（1.14e-4 vs atol 1e-4）
- `39.matmul-trb-pkg-lmdram-256-1024-16` — 境界変種で 360 出力が 1 ulp（1.6e8 で 16.0）

**規模**: 48問、ネイティブ 48+407 実行、比較 3,622,600 値、judge 実行は証人確認の1回のみ。
スコアは `assemble3` の j+m で全48問、合計 680。入力なしの問題は 0（1入力27、2入力21）。

**手法上の注意**: インストール済みのネイティブシミュレータが古かった（10-18 ビルド）ため、
現在の `viz/core`（commit bf08b74）から監査ディレクトリ内で再ビルド。48問の公式テストケースを完全再現。

→ 下限証明は47問で安全に進められる。36 は定義域を 0..511 に制限するか除外する。

## `.double` 窓の意味論と ALU 来歴が着地

ルートビルド: 917 jobs 成功（`DoubleWindowValue`, `ALURequestProvenance` を配線）。

### `DoubleWindowValue.lean`（1452行）
A=0,B=1.0 での `.double` 反駁が成立:
- **初期読み出し値**: 任意バンク/幅/アドレスの初期 PE ファイル読みは `0` か `1.0`。
  PE0 の `.fixed` は下位が `0`/`0x80000000`/`0x80008000`
- **prepared write のデータ**: 整数 request のデータは 2読みの flush 済み `evaluateBus`。
  語2,3 は**第1オペランドの低位 long word のみ**に依存（`evaluateBus_value_low`）→ 目標 `0xBF800000` にならない
- **窓の強制**: 4整列窓4本で16語を覆うと窓は 0,4,8,12 に固定。アドレス 2,3,6,7,10,11,14,15 は
  データ語2,3から書かれる
- **commit カーネル**: `commitParsedMaskedWrites_lm1_word_ne_target`
- **合成**: `ab_not_correct_of_lm1DoubleWindow` と既存の `ab_not_correct_of_lm1WidthNotDouble` から
  `abPE_not_correct_of_widthOrDoubleWindow`（幅で場合分け）

**前提の訂正（重要）**: 「A=0,B=1.0 でデータ語2,3が目標にならない」には唯一の例外がある —
`.immediate payload = 0xBF800000`。これは bus 語2,3 に payload を置くため -1.0 を書き、
右証人では正しい。ただし左証人 A=1.0,B=0（目標 +1.0）では -1.0 を書くので反駁される。
この値比較は未形式化。

### `ALURequestProvenance.lean`（659行）
`alu_*_executionRequest` 族が、具体的な ALU 行について per-write 補題の `request` 仮説を解消。
`DoubleWindowValue` と `request : accesses.op.executionRequest = .ok (.integer precision aluOp)` で接続。

### 残る統合
行ごとの証人データ（左: 幅/個数、右: 整列・被覆・データ安全性）の**無条件な族別インスタンス化**。
`.forward` 源の連鎖不変量、非整数 producer の低位語、immediate 例外の値比較。

## `2.plus-two` の数え上げ下限は破綻、真の障害は入力依存的値来歴

`ProofsLean/PlusTwoBoundSix.lean`（896 jobs）で `LowerBound 4`（条件付き）まで。

**判明した誤り（探索担当の論法に対する反証）**:
- `.double` 宛先は1サイクルで bus 語4つ = **観測語2つ**（奇数アドレス 2k+1）を書く。よって1行は**最大8観測語**、4語ではない
- slot 3 は**純粋な中継**（`IntegerALU.ordinary_lsb_passthrough`）で計算しない
- 全ゼロ証人では20個の目標が全て同じ値 **2** なので、計算した1つの 2 を後続へ中継できる
- したがって「20計算 Long には5行必要」は**定理ではなく発見的論法**。数え上げでは3行すら排除できない

**真の下限には入力依存的命題が必要**: 「出力 k は `input k + 2` を運ぶ計算 Long を必要とし、20個の関数は相異なる」
→ 20計算 Long → 5行 → 定数2を置く行が残らない。

**閉じたもの（無条件）**:
- `plusTwo_score_le_five_length`
- slot 幾何（`parsedDirectAddress_aligned`, `lm1_count_eq_words`）
- `plusTwoPassThroughSlot_is_read_word`（slot 3 は状態語の中継）
- ゼロ入力の初期値（`plusTwoZero_readDirectAccess_zero`, `plusTwoInitialState_forwarding_poison`, `plusTwoZero_fixed_value`）
- **`plusTwoZero_computed_slot_no_two`** — 初期状態では計算 slot に 2 が現れない（1 は `inc 0` で到達可能なので最初の 2 はサイクル1、転送経由）
- `plusTwo_execute_notTwo`（「≠目標」不変量付き数え上げカーネル）
- **`plusTwoLowerBound_four_of_lineBudgets`** — 2つの Prop（行あたり≤8語、初行≤3語）から `LowerBound 4`（3+8+8=19<20）

**残差**: (a) 族別の宛先射影（`ALURequestProvenance` の §3 が plain ALU には使える見込み）、
(b) 入力依存的計算 Long の来歴（真のブロッカー、6 のためには必須）。

**訂正**: `PlusTwoLineCoverage`（行あたり≤4語）は偽。真の値は 8。

## **無条件の反証が完成**: 記録された plus-two 5語解は普遍的に誤り

独立検証: `lake build ProofsLean` → **919 jobs 成功**。
```
#check plusTwoRecorded_not_correct : ¬Correct plusTwoSealedMachine plusTwoSpec plusTwoRecordedAnswer
#print axioms → [propext, Classical.choice, Quot.sound]
```
**仮定なし**。これは Welcome の `Optimal` に次ぐ、問題レベルの2つ目の無条件定理であり、
「出荷済みの解答が間違っている」ことをカーネルで示した最初の結果。

### 支えた2つの汎用成果

**1. ALU request の来歴（依存マッチの解消）** — `ALURequestProvenance.lean`（703行）
- 29個の `alu_<name>_<prec>_executionRequest`（`rfl` で閉じる。`supportsIntegerAt` と `toIntegerOp` が定義的）
- 分岐来歴: `toDirectMaskedIntegerAccessesInLine?_alu_unary` / `_binary` / `_triple`
- 単サイクル: `prepareParsedIntegerALUExprCycle_alu_destination_of_lowered`
- 4サイクル: `prepareParsedIntegerALUExprCycles_destination_map` / `_destination_triples`
  （宛先は `control` の関数、特に `control.context.bar1` 経由）

**2. plus-two の接尾辞 frame** — `PlusTwoSuffixFrame.lean`（794行）
- `plusTwoIdec_lowered` / `plusTwoIxor_lowered`: パラメータ記号のまま lowering を具体化
- 行ごとの frame（語19と BAR1=0 の伝播）を4行連結
- `plusTwoSuffix_preserves_witness_of_bar1`、`plusTwoLine1_preserves_bar1`
- 新しい汎用配管: `executeIntegerProducerLineAtPECore_peContext_eq_of_singleton`、
  `executeIntegerProducerLineAtPEs_peContext_of_not_mem`

→ 依存マッチの射影が**汎用に使える**ようになり、他問題の同種の障害も解消できる。

## 族別宛先一致 `FamilyDestinationCongruence.lean`（1868行）

**閉じた族**: `.matrixRead`（PlainALUDestination と同形式の完全一致 + A−B の族別残差を実際に解消）、
float MAU、msl/msr、float relu、`.matrixWrite`/`.l2bm`（PE を書かないことを証明）。

**共有層**: `parsedStepDestinations`（1ステップの正準宛先列）、`writeParsedMslMsrDestination?_destinations`、
`writeParsedMAUDestinations?_destinations`、汎用 `parsedDestinationFold_destinations`。

**2つの定理形式**:
- リスト返却型（`.matrixRead`）: `maskEq + 両成功 → destination map 一致`
- リスト隠蔽型（float MAU / relu / msl-msr）: 「成功実行が commit するリストの宛先写像は
  (式, 制御, 指令, サイクル列, 初期 bar0/bar1) の純関数」— よって2実行の宛先写像は一致

**残り3族（理由付き）**:
- block float: 原理的障害なし。4PE×4サイクルの入れ子ループへの持ち上げのみ未実施
- L1BM broadcast: 同じく原理的障害なし。PE walk と producer レベルの宛先写像が未完成
- **matrix MAU: 原理的ギャップ**。`writeParsedMatrixMAUDestinationsAtPE` が各宛先を
  per-cycle の **poison フラグ**でゲートし、enabledness がマスクを読むため、
  マスク一致でも poison が違えば準備される宛先列が異なる。**poison/gate の一致仮説**が必要

**副作用条件**: writeDestinations 系では「`.bar` 宛先を含まない」が必要
（`.bar` 書き込みのデータ依存 BAR 更新が後続宛先のアドレス基準を動かす）。

## convert-endian: 固定証人が使えないという発見（全問題に効く）

1. **A−B の幅テンプレートは移行しない**。`cendSpec` は LM1 long word 0（32bit 2語）だけを観測するので、
   どんな `.word`/`.long`/`.double` 窓でも2語に収まり、幅の議論では反駁できない。
   真の障害は**データ**。`cendInitialState` で機械全体の非零語は各PEの LM0 word 0/1（入力）のみ。
2. **固定証人では閉じられない**。反例: 1行 `.pe` で `passa $msb1 → LM1 word 0` は
   入力 `0x0000000000000080` で**正しい**（byteSwap64 が `0x8000000000000000` になるため）。
   定数は行の定数なので、**行自身の定数から証人を構成する**（プログラム依存証人）必要がある。
   → 一様な窓/幅の議論では原理的に閉じない。

閉じたもの: `.matrixRead` 族全体（store が零 ⇒ バス ⟨0,0⟩ ⇒ 全 write が零データ ⇒ 観測対が0のまま）。
残差 `CendPENonMatrixReadRefuted` を `cendPELinesRefuted_iff_nonMatrixRead` で正確に同定。

**教訓（全問題へ）**: 出力が小さい問題では、固定証人だと行がその証人に合わせて正しくなりうる。
下限には**プログラム依存の証人構成**（対角化）が必要。これは今後の共通課題。

## convert-endian: `.matrixRead` 族と不活性族を無条件で閉鎖

`ProofsLean/CendUnconditional.lean`（1072行、63宣言）。

**閉じたもの（無条件）**:
1. **`.matrixRead` 族全体**（任意行数の `.pe` 行）— 初期 matrix store が零 ⇒ バス `⟨0,0⟩` ⇒ 全 write が零データ ⇒ 観測2語が0のまま ⇒ `cendWitness` で ¬Correct
2. **PE レジスタ枠の全行**（`.noforward` / `.wait` / 共有 `.l1bm` 5種）
3. その合併 `CendClosedLines`

**道具立て**: cend 初期状態ライブラリ（forwarding poison、零の matrix store/L1BM/L2BM/DAR）、
観測語カーネル `cend_not_correct_of_lm1_zero`、零データ commit 代数
`commitParsedMaskedWrites_lm1_zero_of_data_zero`。

**残差**: `CendPENonClosedRefuted`（`CendClosedLines` の外の全行）。
`cendPELinesRefuted_iff_nonClosed` で残差 ⟺ `CendPELinesRefuted` を確認。
`CendTwoLinesRefuted` は未着手。

**次に安い族**: `.matrixWrite` / `.l2bm`（PE フレームだが `parsedExprIsPEInertProducer` の外、
matrix 段が `_id` に還元しないので独自の段組み立てが必要）、
L1BM broadcast（初期状態で零データ、`WelcomeL12Shape` の補題あり）。

## `PlusTwoWriteDetermination` は**偽**（契約の設計ミス）

`ProofsLean/WriteDetermination.lean`（538行）。

**反例（機械検証済み）**: `imm 7` を LM1 `.long` 宛先へ、明示マスクセレクタ `$imr1` 付きで書く行。
2つの状態 `writeDetFilesA`（マスク全0）と `writeDetFilesB`（マスク語0/cycle0 = 0xF）は
**全 `WordRef` で一致**する（`writeDetFiles_agree : FilesAgreeOn Set.univ …`）が、
準備される write list が異なり（`writeDetWrites_ne`）、commit される LM1 word 0 が `0` vs `7` になる。

→ `WordRef` はマスクレジスタのバンクを持たず、`wordValue` は lm0/lm1/grf0/grf1/t しか射影しないため、
**`Set WordRef` 内のどんな footprint 拡張でも覆えない**。forwarding スロット、matrix store、
`maskDirective`、`peContext`（BAR/T）、`hazardClock` も同様。

**閉じた部分**: `.nop`、`.mv`、不活性行の `.pe` は任意 footprint で `LineDeterminedAt`。
橋 `not_lineDeterminedAt_of_stepResults_ne`、条件付き `¬ PlusTwoWriteDetermination` も証明。

**修復方針**: 契約を**チャネル対応**にする —
`maskRegisters`、`stateForwardingSlots`、matrix store、`maskDirective`、`peContext`、`hazardClock` の一致を
仮定に加える。`plusTwo_output_forces_footprint_meets` はその契約の下で再導出する。

**教訓**: 「footprint = 銀行語の集合」という設計は不完全。マスクレジスタ等の非銀行チャネルを
契約に含めないと、行の決定性を述べられない。

## チャネル対応の入力依存契約（修復完了）

`ProofsLean/InputDependenceChannels.lean`（860行）。

**契約**: `NonBankChannels` = forwarding スロット、マスクレジスタ、当該 PE の matrix 座標、
`maskDirective`、`peContext`、`hazardClock`。`ChanAgree pe s s'` で比較。

```
LineDeterminedAtChan footprint pe line :=
  バンク語が footprint 上で一致 → ChanAgree → 両方 StepTo →
  ∃ writes, 両方が同じ writes を commit ∧ ChanAgree pe next next'
```

**設計判断**: 結論にも `ChanAgree pe next next'` を含める。これが無いと次の行の仮説が満たせず合成できない。

**再証明**: `execute_agreeOutside_of_determined_chan`、
`exists_footprint_meets_of_output_ne_chan`、plus-two の適用一式
（`plusTwo_output_forces_footprint_meets_chan`、`plusTwo_not_correct_of_footprint_avoids_chan`）。

**解消した行種**: `.nop`（`nop_step_channels`）、`.mv`（`mv_step_channels`）、不活性 `.pe`、
plain-ALU `.pe`（`plain_pe_lineDeterminedAtChan_of_prepared` で実行器の橋まで）。
旧反例 `writeDetMaskedLine` も新契約を満たし、**旧反例は `ChanAgree` で棄却**される
（`writeDetCounterexample_excluded`）。

**残差2つ（Prop、公理ではない）**:
1. `PEPreparedListCongruent` — 準備リストがチャネル+footprint の関数であること
   （`prepareParsedMaskedWriteWithForwarding_congr_of_agree` を4サイクル×式リストへ持ち上げ）
2. `PEChannelFrame` — 行後もチャネルが一致すること（walk の frame + per-PE 更新）

**教訓**: footprint を「銀行語の集合」と定義すると、マスクレジスタ等の非銀行チャネルを見落とし、
行の決定性を述べられない。契約には全チャネルを含める必要がある。

## ネイティブ公理（`bv_decide`）の除去

`ProofsLean/ByteSwapKernel.lean`（552行）で `byteSwap64` の全単射を**構造的に**証明。
`bv_decide` を使わず、バイト抽出（`Nat.testBit_mul_two_pow`）で 8 バイトを反転再構成する。

- `byteSwap64Kernel_involutive` などは `[propext, Quot.sound]` のみ
- `byteSwap64_injective_kernel` は `[propext, Classical.choice, Quot.sound]` のみ

**配線**: `ProgramWitness.byteSwap64_injective` の証明本体を `byteSwap64_injective_kernel` に置換。
```
#print axioms cendPE_not_correct_of_candidatePair
→ [propext, Classical.choice, Quot.sound]   （以前は ..._native.bv_decide を含んでいた）
```
ルートビルド: 927 jobs 成功。

**残るネイティブ公理**: `ConvertEndian.answerDatapath_is_byteSwap`（`ConvertEndian.lean:288`、
64bit の `bv_decide`）。これに依存する `answerDatapath_involutive`、
`abstractConvertEndian_is_byteSwap`、`answerProgram_parsed_second_line_readback`、
`answerMemoryCycle_byteSwap` は未だ汚れている。構造的証明が別途必要。

**教訓**: 64bit の `bv_decide` はネイティブコードにフォールバックし、公理を導入する。
「証明支援系で検証済み」と言う前に `#print axioms` を見る必要がある。

## チャネル契約の残差を解消（`ChannelResiduals.lean`、2381行）

**項目1 閉鎖**: `PEPreparedListCongruent`（plain-ALU 族）。
`prepareParsedIntegerALUExprCycle_congr`（9分岐の完全解析、write list とスロットの一致）→
`prepareParsedIntegerMatrixReadLineCycles_congr_plain` → `pepreparedListCongruent_plain`。
残る前提は footprint 被覆のみ。

**項目2 は偽と判明**: `PEChannelFrame` は導出不能。
`updateParsedIntegerALUForwardingCycle_installs_data` が per-cycle の forwarding 更新で
`.known (pack write.data)` を入れ、`forwardingValueValid .known = true` になるため、
読む `.pe` 行は「読んだバンク語に依存する形で」forwarding チャネルを変える。
→ 修復版 `PEChannelFrameOn`（バンク一致を仮定に加える）を定義し、plain 行で機械検証。

**plus-two の到達点**:
- `PlusTwoWriteDeterminationChan` が `DischargedLine`（nop / mv / plain-ALU `.pe`）のプログラムで成立
- `plusTwo_not_correct_of_concrete_footprint_avoids_chan_of_discharged`
  — 「入力 j を読まないプログラムは誤り」が具体 footprint と新契約で**端から端まで**
- `plusTwo_output_forces_footprint_meets_chan_of_discharged`

**残差1つ**: `PlusTwoLineFootprintCoversPreparedReads` —
hazard-event の footprint（`ParsedExpr.toTimedPEHazardEvents?`）が 9分岐 lowering の読む全語を覆うこと。
**2つの lowering の突き合わせ**で、未解消。

**未解析**: 非 plain 族と不活性 `.pe` 行（後者は同じ道具立てで証明できそう）。

**教訓（2度目）**: 契約は2度偽と判明した（`PlusTwoWriteDetermination` → バンク語だけでは不足、
`PEChannelFrame` → チャネルだけでも不足、バンク一致も要る）。仮説を立てる前に
「その仮説で結論が導けるか」を機械検証する必要がある。

## `PlusTwoLineFootprintCoversPreparedReads` も**偽**（3度目の契約反証）

2つの独立な障害（いずれも plain 族の内部）:

1. **`.zero`/`.immediate` 行**: `parsedExprIsPlainIntegerALU` はこれらも真で、
   `parsedExprIsIntegerMatrixReadStageInput` も真なので `preparedListReadSet` に入る。
   しかし実行器の masked 定数書き込みは**宛先の read-modify-write**（両ソースが `.memory destinationAccess`）で、
   準備読み集合に `accessRegion destinationAccess` が入る。
   一方 `ParsedExpr.toTimedPEHazardEvents?` は `.zero` 行では宛先の**書き込み**イベントのみを報告し、
   `peLineSourceAccesses` が書き込みを除くので `plusTwoLineFootprint = ∅`。
   → 準備可能な `.zero` 行で必ず包含が破れる。**hazard footprint の実質的な穴**。
2. **`.alu` 行でも過大**: `toTimedPEHazardEvents?` は行のソースについて all-or-nothing
   （1つのソースで `toDirectMemoryAccessMode?` が失敗すると行全体が `none`）だが、
   `preparedListReadSet` は無条件に定義される。両方を混ぜた行で読み集合が非空・footprint が空になる。

**帰結**: `plusTwoWriteDeterminationChan_of_all_discharged` と
`plusTwo_not_correct_of_concrete_footprint_avoids_chan_of_discharged` は
`covers` 前提が充足不能なため**空虚**だった。

**修復**: 行を `op = .alu` かつソースが addressable（`ParsedOperand.directMemoryAddressModeValid`）に制限するか、
「準備に成功する行」に限る。その制限下での核となる整合は既に証明済み:
- `toDirectMemoryAccessMode?_mask_allow_irrelevant` — 実行器の `toDirectMemoryAccess?` と
  hazard 側の `toDirectMemoryAccessMode? (forHazardAddress operand) true` が一致
- `exists_read_event_of_memory_resolution` — `.mem` ソースが解決されるなら hazard 側の
  非書き込みイベントの access が同じ

`DischargedLine` から `.zero`/`.immediate` を落とす必要がある。

**教訓（3度目）**: 残差と称した命題を3つ書いて3つとも偽だった。仮説を置いたら、
その可用性（充足可能性）まで機械検証しないと、条件付き定理が空虚になる。

## plus-two の入力依存カーネルが**無条件**に

`ProofsLean/ALUReadSetBound.lean`（1198行）。ルートビルド 930 jobs。

**8つのリゾルバすべてに読み出し集合上界を証明**:
`maskedIntegerReads` / `maskedListReads` / `maskAccessesReads` / `noWriteAccessesReads` /
`barAccessesReads` / `maskInputAccessesReads` / `maskMemoryThenInputReads` / `maskInputThenMemoryReads`
— いずれも `⊆ sourceReadUpperBound`。和集合版 `aluCycleReadSet_subset_sourceReadUpperBound`。

**修復された残差は定理に**:
```
preparedListReadSet_subset_plusTwoLineFootprint :
  plain かつ全行が .alu かつ全オペランドが addressable →
  preparedListReadSet … ⊆ plusTwoLineFootprint (.pe expressions) state
```

**無条件の連鎖（残差引数ゼロ）**:
```
DischargedALULine        := nop ∨ mv ∨ (.alu 行のみの .pe)
plusTwoWriteDeterminationChan_of_aluRows
plusTwo_not_correct_of_concrete_footprint_avoids_chan_of_aluRows
  : プログラムの全行が DischargedALULine で、入力 j を読まないなら ¬Correct
```
検証済み（`#check`、axioms は標準3つのみ）。

**実装メモ**: リゾルバ7-8 は依存マッチャになり `cases` が失敗するため、
`sources` を自分で `cases` → `simp only [resolver] at lowered` → `repeat' split at lowered` → `simp_all`。

**注**: 元の `PlusTwoLineFootprintCoversPreparedReads` は `.zero` 行で反証されるため残置（偽）。

→ plus-two の「入力依存的」な下限の土台が完成。次は数え上げ（20出力・定数2）との合成。

## **初の無条件下限**: plus-two の `2 ≤ score`

`ProofsLean/PlusTwoCompose.lean`（1311行）。ルートビルド 931 jobs。

```
plusTwo_lowerBound_two :
  (全行が DischargedALULine) → Correct plusTwoSealedMachine plusTwoSpec program →
  2 ≤ score plusTwoSealedMachine program
```
`#print axioms` → 標準3つのみ。**残差引数ゼロ**。

### 読み出し容量は 8（実モデルから導出）
```
plusTwoFootprint_inputs_card_le_eight :
  SourceRegionsAgree → {j | inputWord j ∈ footprint (.pe expressions) state}.card ≤ 8
```
導出: `.pe` 行の行数は制限されない（行はリスト全体を歩く）が、
issue checker の `readsAgree` が同一バンクの `.mem` 読みに**同一 `Region`** を強制し、
`Region` は幅と4サイクル分のアドレスを固定する → LM0 アクセスは**4つだけ**。
入力語は奇数アドレスなので4語窓に高々2個 → 4×2 = **8**。

### 素朴な `20/8 → 3行` が塞がれる理由
カーネルの証人は**状態存在形**で、解決アドレスが状態の BAR 語を含む
（`(bar0 + regionAddressAt cycle + madpe)/words*words`）。bar0 を動かすと同じ行が**全入力語を読む**ため、
「行あたり≤8」は (行, 状態) ごとの事実で行数を縛らない。
→ **prefix に証人を固定する強化** `plusTwo_exists_prefix_footprint_meets_chan` で解決。
1行プログラムは prefix が空なので両証人が初期状態になり、初期 footprint は入力非依存（`plusTwoInitialState_footprint_eq`）。

### 到達点
- `LowerBound 2`（**無条件**、discharged クラス）
- `LowerBound 3` は `PlusTwoInitialFootprintCoverage` 条件付き（`20 ≤ 8 * length` の合併上界）
- `LowerBound 4` は**書き込み**側の予算から（読み出しは寄与しない）
- 5/6 は**この形の数え上げでは不可能**（1行あたり ≤4/≤3 入力語が必要で、footprint は与えない）
  → 入力依存的値来歴が必要（`PlusTwoOutputProvenance`）

## 残存仮説の監査（`RESIDUALS.md`）

全198宣言（`LowerBound` 系66、`¬ Correct` 系142）を走査。

### 無条件の `LowerBound` は3つだけ
Welcome 2（`WelcomeOptimalFinal.lean:159`、whole-machine 版と partial 版を含む）、Welcome 1、PlusOne 2、
および証明書の消費者。AB / Cend / PlusTwo≥3 / Mul7 / AplusB の無条件下限は**無い**。

### 偽と判明した残差（それを使う条件付き定理は空虚）
| 残差 | 反証 |
|---|---|
| `PlusTwoLineCoverage` | 幅広 `.zero` 行（`PlusTwoSuffix.lean:249-320`） |
| `PlusTwoLineFootprintCoversPreparedReads` | `.zero` の RMW（`FootprintCoverage.lean:565`） |
| `PlusTwoSuffixPreservesWitness` | `PlusTwoSuffix.lean:327` |
| `WelcomePEWriterKindDataResiduals` / `...Three` / `WelcomePEL1BMWriterData` | `WelcomeWriterPackages.lean:885,1032,1147,1154` |
| `WelcomePEMixedPlainInertFlagAgreement` | `WelcomeFlagAgreement.lean:331` |
| **`PlusTwoInitialFootprintCoverage`** | **意味的に偽**。BAR を使う11行反例（全行が `DischargedALULine`） |

→ `plusTwoLowerBound_three_of_coverage`、`plusTwoLowerBound_five_of_coverage`、
`plusTwoWriteDeterminationChan_of_discharged` などは**空虚**。修復版（`PlusTwoALULineFootprintCoversPreparedReads`、
`plusTwo_not_correct_..._of_aluRows`、`plusTwoRecorded_not_correct`）は生存。

### 開いている（反証されていない）
AB の2残差、Cend の2残差、PlusTwo の write budgets、`PlusTwoWriteDeterminationChan`（一般形）、
`Mul7PELineFootprint`、AplusB 残差、Welcome の plain/matrixRead パッケージ。

### 監査で判明した重要な事実
`PlusTwoOutputProvenance` は**無条件に真**（かつ未使用）。仮説として使えば生存する。
`PlusTwoInitialFootprintCoverage` の反例は、BAR を書く `.alu .lnot` 行＋LM1 経由の2パスで
`input+2` を計算するもので、**意味的には偽**（形式的反証は4096PE walk の持ち上げが未了）。

**教訓の再確認**: 条件付き定理は、その仮説が偽なら空虚になる。今回は6つの残差が偽と判明し、
それを使う定理が空虚だった。`RESIDUALS.md` に全件の生存/空虚を記録した。

## convert-endian: plain-ALU 族を**1つの残差**に還元

`ProofsLean/CendPlainWitness.lean`（696行、42宣言）。ルートビルドへの配線後に確認。

**閉じたもの（無条件）**:
- `cendLineReadSet` と `cendLineReadSet_eq`（全チャネル引数が入力非依存）
- **因数分解** `cendPE_plain_prepared_eq` — 2入力が読み集合を覆う半分集合で一致すれば、
  準備リスト・転送スロット・BAR リストが一致（`ChannelResiduals.prepareParsedIntegerMatrixReadLineCycles_congr_plain`
  + `ProgramWitness.cendInitialPERegisters_agree_of_halves`）
- **観測対の決定** `cendPE_plain_determined`
- **無条件の反駁** `cendPE_plain_not_correct_of_readSet` / `_of_avoidsHigh` / `_of_avoidsLow`
  — 読み集合が LM0 word 0（または 1）を含まない plain 行は誤り
- `cendPE_plain_not_correct` → `cendPE_plainLines_not_correct` → `cendPENonConstantRefuted_plain`
  （**定数族も再カバー**、`¬CendClosedLines` 仮説不要）

**残差は2つ**:
1. `CendPlainALUBothHalvesRefuted` — 読み集合が LM0 word 0 と 1 の**両方**を含む plain 行。
   衝突論法の外（区別できない2入力は目標も等しい）。`.long`/`.double` の広い窓族で、
   有限オペコード表による `CendPlainALUWideWitness` のidea が必要
2. `CendLineReadSetLm0Words` — `accessRegion` の列挙。**依存除去の失敗**で阻害
   （`DirectMemoryAccess.address` の `Fin` 証明がアドレス値に固定されるため）
   **修正案**: `cendResolvedLm0Address` を新しい Nat 証人 `start`（+ `start = access.address.val`）で
   述べ直せば、`Finset.mem_image` で閉じる

→ 修正案 (2) が通れば narrow 族が端から端まで無条件になる。

## convert-endian: 橋を修復、narrow 族が**無条件**に（7つ目の偽残差も発見）

`ProofsLean/CendReadSetBridge.lean`（615行）。

**Nat 証人による修復は成功**:
`cendResolvedLm0AddressNat`（`start = access.address.val` を伴う）を証明し、
`accessRegion_word_val` / `accessRegion_word_val'`（依存除去を回避）を経て
`cendOperandLm0WordsCoverReads_proof` が成立。

**7つ目の偽残差**: `CendLineReadSetLm0Words` は**偽**。
`.zero`/`.immediate` 行は plain で段フィルタを通るが、`sources = []` なのに実行器の2ソースは**宛先自身**なので、
準備読み集合に宛先の LM0 領域が入る。
`zeroRow_cend_readSet` / `cendLineReadSetLm0Words_false` で機械検証。
→ これを使う `cendPE_plain_not_correct_of_words/_of_wordsLow` は空虚。

**正しい橋**: `CendALUOperandLm0WordsCoverReads`（全 `.alu` 行版）を証明。

**無条件で閉じた narrow 族**:
```
CendPlainALUNarrow := (全行が .alu) ∧ (0 または 1 が LM0 words に無い)
cendPE_plainALUNarrow_closed : CendPlainALUNarrow → ¬Correct [.pe expressions]
cendPENonConstantRefuted_plain_narrow   -- 残差なし
```

**残差の再整理**: 全 `.alu` 族は構文的残差 `CendPlainALUWordBothRefuted`
（読み集合が語0と1の両方を含む）に還元。narrow 側は無条件。
広い `.long`/`.double` 族が真に開いている部分。

**教訓（7度目）**: 「plain 行」という述語は定数行も含むため、ソース語の議論には `.alu` 制限が必須。

## convert-endian: 広い族を「LM1 宛先あり + 両半分読み」に狭窄（無条件部分を拡大）

`ProofsLean/CendWideWitness.lean`（1982行）。

**無条件で閉じたもの**:
- 有限値域カーネル: `exists_not_mem_of_card_lt`、`cendPE_not_correct_of_eventually_range`、`..._smallRange`
  （途中で詰まる入力は既に不正解として扱える）
- 観測1語カーネル: `cendZeroLowPairs`（card ≤ 2^32、目標1を含まない）、双対 `cendZeroHighPairs`
  → `cendPE_not_correct_of_lm1_word_one_free` / `_zero_free`
- 実行器の宛先側（9分岐すべて）: `prepareParsedIntegerALUExprCycle_noLm1` → 行・fold へ持ち上げ
- **`cendPE_plain_not_correct_of_avoidsLm1`** — 静的 `(.lm1, _)` 宛先を持たない plain 行は**無条件で反駁**
  （LM1 バンクが初期ゼロのまま）。非空性 `cendNoLm1Line` も証明。

**狭窄された残差**: `CendPlainALUBothHalvesRefutedLm1` = 両半分読み **かつ** 静的 LM1 宛先を持つ plain 行。
`cendPlainALUBothHalvesRefuted_of_lm1Destination` で旧残差を含意。
`cendPE_plainLines_not_correct_of_lm1Destination` で plain 族全体をここから反駁。

**残る義務**: その行について有限値域の値解析（(a) 目標の外に出る有限集合 S を構成、または
(b) 観測 LM1 語が書かれないことを示す）。前担当の注記: 転送で ALU 結果を合成する複数行では
狭窄残差が偽になりうる（未調査）。

**注意**: 有限オペコード表の列挙は未実施。`CendPlainALUBothHalvesRefuted` 自体は未証明。

## convert-endian: 狭窄残差は**真**（反例なし）と確定、値解析も完了

`ProofsLean/CendLm1Witness.lean`（826行）。ルートビルドに配線。

### 充足可能性の検証（反例なし）
- `cendDatapathWords` が証人入力 `0x0123456789abcdef` で単一 ALU データパスが bus に置ける
  **全12000語**（3精度 × 20演算変種 × 100ソース対 × 2 bus 語 = 128 相異値）を列挙。
  `cendDatapathWords_avoid_high/_low` で目標 `0xefcdab89` / `0x67452301` が含まれないことを機械検証
- ソース bus 族が初期状態で**完全**であることを証明（`cendMemoryBus_mem`、`cendFixedBus_mem`）
- 実行器自身の準備コードで 2528 行 × 16 入力を実行 → **0 正解、0 スタック**
- `.long` passa は恒等、`.half` bsl は16bitレーン交換のみ、`.double` は恒等+零

### 前担当の懸念（複数行で転送合成）は**起こらない**
`cendInitialForwardingSlots_poison`（初期転送スロットは全て poison）で `.forward` ソースは全入力で失敗。
さらに `executeIntegerProducerLineAtPECore` は**全行を同じ行前ファイル**から準備し、
commit も行前ファイルへ行うので、前の行が書いた LM1 語を読む行は行前の 0 を見る
（`cendLm1ComposeLine_witness = some (0x01234567, 0)` で機械検証）。

### 証明済み
- `CendLm1WordObligation` から `cendPlainALUBothHalvesRefutedLm1` を導出
- **`cendPE_not_correct_of_inputIndependentPair`** — 観測対が2入力で同じなら反駁
  （目標が単射かつ非定数）。`.zero`/`.immediate`/flush 零出力を値解析なしで閉じる

### 残差は**配管のみ**
`CendLm1WordObligation`（plain 両半分行 + LM1 宛先）を実行器から出す部分。
値解析は完了しており、`WelcomeProvenance.prepareParsedMaskedWriteWithForwarding_memory_eq` と
`prepareParsedIntegerALUExprCycles_four_general` で組み立てるだけ。数学的な残りは無い。

## 設計判断 (ii) は**不健全**だった / `CendPELinesRefuted` は plain 族から従わない

### 1. 半マスクの合成（私の判断ミス）
私が指示した「値集合を `{d, d &&& 0xffff0000, d &&& 0x0000ffff}` に拡張」は**不健全**。
1行の4サイクルは全て commit され、同一行が同じ LM1 アドレスを補完的な半マスクで複数サイクル書ける。
その結果、**2つの異なるデータパス語の混合**が生じる。

機械検証された具体例（証人入力で `#eval!`）: 行 `.alu .add (some .s)`、ソース `[lm0 0..3, 0,0,1,1]`、
宛先 `[omr 1, mem lm1 word 0 with mask (.entry false 1)]` が LM1 word 0 に `0x13564567` を commit。
これは hi16(`0x13569bde`) ++ lo16(`0x01234567`) で、単一データ語の形でも部分マスクでもない。

**修復**: 値集合を**半混合閉包** `{ hi16(d1) ++ lo16(d2) : d1,d2 ∈ cendDataWords }` に拡張。
証人ではデータパス語の high16 が `0xefcd`/`0x6745` でも low16 が `0xab89`/`0x2301` でもないことが
`decide` で確認済みなので、半混合は目標にならない。commit 不変量は任意の半マスク付き
`mergeSelectedWord` で閉じる（`selectedWordMask` は index 0/1 で常に 0/allOnes/high/low）。
`ProofsLean/CendHalfMix.lean` がこの代数でビルド済み。

### 2. クラス包含の誤り
`CendPELinesRefuted` は `CendPlainALUBothHalvesRefuted` から**従わない**。
後者は全行が `.alu`/`.zero`/`.immediate` の行のみをカバーする。
混合行と非 plain 族（float MAU/relu/block-float/msl-msr、matrix MAU、matrixWrite、L1BM broadcast、L2BM）は
ツリー内に反駁が無く、`CendUnconditional` の残差 `CendPENonClosedRefuted` が
`cendPELinesRefuted_iff_nonClosed` で正確に同値と述べられているとおり。

→ 最終連鎖は **plain 族で止まる**。`LowerBound cendSealedMachine cendSpec 2` を主張するには
非 plain 族の反駁が別途必要。

### 教訓（8度目）
「値集合を拡張すれば済む」という私の判断は、**サイクル間の合成**を見落としていた。
1行の中でも複数サイクルの書き込みが同じ語に重なるため、単一データ語の像では足りない。

## 半混合閉包による修復が着地（convert-endian LM1 値層）

3ファイルをルートに配線。**939 jobs 成功**、132モジュール、131 import。

- `CendHalfMix.lean`（563行）: `cendHalfMixWords = {hi16(d1) ++ lo16(d2) : d1,d2 ∈ {0} ∪ cendDatapathWords}`、
  `cendDatapathWords_targetHalves_avoid`（12000語表への1回の `decide`）、
  `selectedWordMask_lt_two_cases`、`mergeSelectedWord_halfMix_mem`（閉包性）
- `CendCommitMix.lean`（185行）: `distance_lm1_lt_two`（整列で data index < 2）、
  commit fold が半混合集合を保つ
- `CendFinal.lean`（392行）: `CendHalfMixWordObligation`、そこから
  `cendPlainALUBothHalvesRefuted_of_halfMixObligation`、
  `cendLowerBound_two_of_plainHalfMix_and_nonClosed`

**私の設計判断 (ii) は不健全で、半混合閉包が正しい**ことが機械検証で確定。
`cendLm1WordObligation_toHalfMix` により旧義務が新義務を含意するので、拡張で失うものはない。

**残り（正確）**:
(A) `CendPlainCycleHalfMixData` — 9分岐の executor assembly。材料は全てツリー内。
(B) 非 plain/混合族（float MAU/relu/block float/msl-msr、matrix MAU、`.matrixWrite`、
    L1BM broadcast、L2BM）は未反駁。`CendPELinesRefuted` はここで止まる。

→ `LowerBound cendSealedMachine cendSpec 2` は**未到達**。plain 族の assembly と非 plain 族の反駁が必要。

## convert-endian: **plain 族が完全に無条件で閉鎖**

`CendCycleData.lean`（2552行）+ `CendCycleClose.lean`（238行）をルートに配線。

**無条件で証明**:
- `cendPlainCycleHalfMixData`（9分岐の per-cycle データ分配）
- `cendPlainCycleLm1Aligned_general`（整列）
- `commitParsedMaskedWrites_lm1_halfMix_halfMix`（半混合版の commit 閉包）
- `cendPlainALURow_dataAndAligned`（4サイクル持ち上げ）
- **`cendHalfMixWordObligation_of_plain`** — §4(a)+(b) を plain 行で解消
- **`cendPlainALUBothHalvesRefuted`**（無条件）
- **`cendPE_plainLines_not_correct_unconditional`** — plain 族の反駁
- `cendLowerBound_two_of_nonClosed_plainDischarged` — plain 仮説を解消した `LowerBound 2`

行レベルの鍵: 受理された plain 行は**行を高々1つ**しか持てない（`plain_legal_length_le_one`）ので、
`.alu (some p)` / `.zero` / `.immediate` の3分割で済む（`.alu none` は不可能と証明）。

**残差は1つ**: `CendPENonClosedRefuted` — 非 plain 族（float MAU、matrix MAU、matrixWrite、
L1BM/L2BM、msl/msr、block-float/relu、混合行）。plain 族の残差は**ゼロ**。

→ `LowerBound cendSealedMachine cendSpec 2` は「非 plain 族の反駁」だけに条件付く。

## convert-endian: 非 plain 族のうち2族を閉鎖、残差を `CendNonPlainResidual` に狭窄

`ProofsLean/CendNonPlain.lean`（930行）を配線。

**無条件で閉じた2族**:
- `.matrixWrite` + `.l2bm`（+ 既存不活性）— 新クラス `cendPEInertProducerExt`、
  行レベルの frame `executeIntegerProducerInstructionLine_pe_peRegisters_of_extInert`、
  反駁 `cendPE_extInertLines_not_correct`
- **L1BM broadcast** — `cendInitialState_l1ToPEBusAt_zero` から零データ連鎖
  （`..._writeDestinations_lm1_zero` → `..._AtPEs_lm1_zero`（4096 PE）→ `..._Producers_lm1_zero`）、
  反駁 `cendPE_l1ToPEOrExtInertLines_not_correct`

**残差**: `CendNonPlainResidual` — `cendL1ToPEOrExtInert` の外の行を1つ以上含む行。
`cendLowerBound_two_of_nonPlainResidual : CendNonPlainResidual → LowerBound cendSealedMachine cendSpec 2`。

### 私の前提の誤り（9度目）
「float MAU の bus の下位32bit は 0 だから零データで落ちる」は**誤り**。
`doubleMAUVectorBus_low` が零にするのは unpack 語 **2,3** のみで、観測語 0,1 は `bus.high`（64bit ベクトル）から取る。
実測: `mau .h .mul` に `.long` 宛先（アドレス0）で lm1[1] = 0x43394000 ≠ 0。
→ 零語ルート（`cendPE_not_correct_of_lm1_word_one_free`）では float MAU / msl-msr / `.long 0` 窓は閉じない。
**本物の値議論**が必要（証人では読み bus が10族に尽きるので、可能なベクトルを `decide` で列挙できる）。

### その他の訂正
- matrix MAU と block float は **PE 不活性ではない**（`physicalPEId coordinate pe` に commit、block float は lowering 宛先へ書く）
- msl/msr は `.mem` 以外のソース形状で `.unknown`（スタック）
- relu/block-float は初期状態で単純形状だと `.unknown`/`.failure` が多い

**次の安い拡張**: matrixRead の零データ抽出を「段入力行が matrixRead か `.noforward`、
残りが ext-inert/broadcast」へ一般化。新規の値解析は不要。

## convert-endian: 混合行を閉鎖、残差が「値を持つ族」だけに

`ProofsLean/CendMixedRead.lean`（781行）を配線。

**閉じたクラス**: `CendMixedReadLines`（段入力が `.matrixRead` か `.noforward`、残りが ext-inert/broadcast）。
鍵は `cendMixedReadRow_stageInput`（混合行が段入力なら必ず `.matrixRead` か `.noforward`）。
`.l2bm` は `cendL1ToPEOrExtInert` を通るが整数 walk から外れる。

**証明**:
- 緩和抽出 `prepareParsedIntegerMatrixReadLineCycles_data_zero_of_readOrNoForward`
- per-PE broadcast frame `executeParsedL1ToPEProducers_lm1_zero_at`
- walk 抽出 `cendMixedReadWalk_prepared`、行レベル `executeIntegerProducerInstructionLine_pe_lm1_zero_of_mixedRead`
- `cendPE_mixedReadLines_not_correct`

**狭窄残差** `CendMixedReadResidual`。**厳密性を証明**:
`cendNonPlainResidual_iff_mixedReadResidual`、`cendLowerBound_two_iff_mixedReadResidual`
（何も弱めていない）。**非空性**も `cendMixedExampleLine_new` で証明
（`[.matrixRead .d, .l1bm .pbcast]` の行が以前は残差内、今は反駁済み）。

→ 残るのは値を持つ族のみ: plain ALU（別途済）、float MAU、float relu、msl/msr、matrix MAU、block float。

## convert-endian: msl/msr 族を閉鎖、**再利用可能な値議論の型**を確立

`ProofsLean/CendValueFamilies.lean`（1331行）を配線。

**閉じた族**: `CendMslMsrLines`（全行が `.matrixRead`/`.noforward`/ext-inert/msl-msr）。
`cendPE_mslMsrLines_not_correct`、厳密分割
`cendMixedReadResidual_iff_mslMsrResidual`、非空性 `cendMslExampleLine`。

**確立した型（他族に再利用）**:
1. `cendMixWords L` = 任意の32bit語リストの**半混合閉包**（`cendHalfMixWords` の一般化）。
   `mergeSelectedWord_mixWords_mem` と汎用 commit 補題 `commitParsedMaskedWrites_lm1_mixWords`
2. `cendFlush_data_mixWords` — 任意フラグの flush は16bit半分を零にするだけなので、
   観測データ語はソース語の半分の閉包に留まる（`revert flags; decide`、bv_decide 不使用）
3. 証人での生成リスト `cendMslWords`、`0x08070605 ∉ cendMixWords cendMslWords` をカーネル検査
4. 来歴: msl/msr のソースは `mslMsrSourcePE`（⟨3⟩/⟨1⟩）で読まれ、全 PE が同じ初期ファイルを持つ。
   `CendLm1Obligation.cendSourceOk_*` を隣接 PE 文脈へ一般化（fixed の場合の新補題付き）
5. データを持つ段の連鎖（宛先 fold → 4サイクル → 4096-PE walk → producer）
6. 行の組み立て（整数段は零データ、msl 段が家族データ、relu/block/matrixMAU は frame、L1 段は空）

**確認**: `mslMsrOutputBus source = ⟨source.high, 0⟩` なのでデータ語は `source.high` の半分。
**「下位語が零」論法は本当に使えない**ことが証明で裏づけられた。

**残差** `CendMslMsrResidual`:
(a) msl 行と L1BM broadcast 行の混合（broadcast 段のデータ付き commit が未了、安い見込み）
(b) float relu / block float / matrix MAU / float MAU（未着手）
(c) plain ALU 行と値行の混合（plain の per-cycle データを混合整数段へ持ち上げる必要）

**次へのヒント**: block float / matrix MAU は証人での生成リストを構築し、
**半分（hi16/lo16）での目標検査**にする（閉包全体の `decide` は大きすぎる）。
`cendPlainCycleHalfMixData_general` は全 plain 単一行のみなので、混合整数段には新規作業が要る。

## convert-endian: block float / matrix MAU の値代数と目標回避が完成（族の反駁は未完）

`ProofsLean/CendMatrixFamilies.lean`（1050行）を配線。

**証明済み**:
1. **目標回避代数** `CendHalvesAbsent L hi lo` — 生成リスト上の線形検査のみ（閉包全体の `decide` を回避）。
   `cendMixWords_ne_of_halves` などで閉包の非所属に落ちる。
2. **block float の生成リスト** `cendBlockFloatWords` — 10初期 bus 上の `parsedBlockFloatMab` の高語半分
   + 6つの固定パターン、25ケース（d/f/g/h、keep 0..10 × bfn/bfe）。
   カーネル検査 `cendBlockFloatWords_avoid` で目標半分の非所属を確認。
3. **matrix MAU の生成リスト** `cendMatrixMAUWords` — 零 store の零行パック（全精度/round/lane）と、
   `.fma` の PE 読みアキュムレータ（10 bus × 8 属性組合せ）。`cendMatrixMAUWords_avoid` で非所属を確認。
   `parsedMatrixMAUDestinationDataPoisonApplies_false`（poison=false のゲート）も証明。
4. **データ橋・段の連鎖** — `writeParsedMslMsrDestination?_data_mixWords`、
   `executeParsedBlockFloatAtMAB_{apply,writePEs,runCycles}_data`、定数読みの値定理一式。
5. **正確な残差** `CendMatrixFamiliesResidual`（block float / matrix MAU を除外した形）、
   `cendMslMsrResidual_iff_matrixFamiliesResidual`、`cendLowerBound_two_of_matrixFamiliesResidual`、
   非空性 `cendBlockFloatExampleLine_new` / `cendMatrixMAUExampleLine_new`。

**残り（2つの Refuted Prop のため）**:
(a) 4レーン・ソース来歴 — `.mem` ソースはレーン間で `madpe` 前置だけ異なるので、読みベクトルは
    2 bus の接頭パターン a…a b…b。`toDirectMemoryAccess?` の開始アドレス式が必要
(b) 1024 座標の MAB walk + 行組み立て
(c) `.h` の keep > 10 の折り畳み（`keep 10` に落ちる）
(d) matrix MAU の宛先 fold（poison ゲート + `.omr` 検査）と cycle/MAB/段の連鎖

# **「最短確定」第1号: `1.plus-one`（Welcome）**

## 公開仕様の確認（監査の懸念は事実誤認だった）

`problems/challenge/1.plus-one/problem.md` の `## Inputs`（141-143行、機械生成で判定に効く）:
```
X (0 ≤ X[i] ≤ 50): Int $lm[0:16], /((8:1, 2_W:1); B@[PE,MAB,L1B,L2B])
Y: Int $ln[0:16], /((8:1, 2_W:1))
```
- **定義域は `0 ≤ X[i] ≤ 50`** — まさに `welcomeSpec.admissible`。監査の Caveat 1 は**誤り**
  （prose 本文にだけ制約が無い）。なお `PlusOne.Words = Fin 16 → BitVec 32`（64bit ではない）
- `B@[PE,MAB,L1B,L2B]` は全 PE へのブロードキャスト — `welcomeInitialState` と一致
- **post は PE0 の16語** — `testcase.vsm` は `d getd $ln{0,2,…,14}n0c0b0m0p0` のみ。
  Caveat 2 は正しいがギャップではない（PE0 のみが判定対象）

→ `welcomePublicSpec` は `welcomeWholeSpec` と**定義的に同一**（`rfl`）。
**既存の無条件定理がそのまま公開問題の定理だった。**

## 証明（`WelcomePublicSpec.lean`、402行）

| 定理 | 定義域 | 観測 |
|---|---|---|
| **`welcomePublicMachine_optimal`** | `0..50` | PE0（**公開仕様そのもの**） |
| `welcomePublicBoundedAllPEs_optimal` | `0..50` | 全 PE |
| `welcomePublicUnbounded_optimal` | 全 `BitVec 32` | PE0 |
| `welcomePublicAllPEs_optimal` | 全 `BitVec 32` | 全 PE |

新規の数学:
- `welcomeLineReadbackAt` — `welcomeLineReadback` を任意 `PEId` へ一般化
- `welcomeSealedAnswer_values_allPEs` — **非有界入力かつ全4096PE**。
  旧証明の `_admissible` は未使用で commit が PE 一様だったため、実質的な一般化
- `lowerBound_of_harder_spec` — 定義域拡大 + post 強化 ⇒ `Correct` が難しい ⇒ 易しい spec の下限が移行
  （方向の誤りが無いことを明示）

検証: `lake build ProofsLean` → **946 jobs 成功**、`#print axioms welcomePublicMachine_optimal`
→ `[propext, Classical.choice, Quot.sound]`。

## 到達点

- 上限 **2語**（`welcomeAnswer`、公式 judge で ACCEPTED）
- 下限 **2**（`welcomePublicMachine_lowerBound_two`、無条件）
- **一致 → `1.plus-one` は最短確定**

## convert-endian: 「最小3語」の根拠が半マスクで崩れる（要再検証）

`ProofsLean/CendTwoLines.lean`（750行）を配線。ルート 947 jobs。

**証明済み（`CendPELinesRefuted` を仮定して）**:
- コスト1行の分類 `cendCostOne_cases`
- 枠だけの2行目（`nop`/`mv`/全 `.noforward`）は**任意の1行目に対して**反駁
  （`cendTwoLines_second_frame_not_correct`）
- `nop/1` と `mv` の1行目は時計と pendingMv しか渡さない
- 初期 forwarding は poison、`.forward` 読みは失敗
- 全面マスクでは半分の混合は起きない（`cendCommitChain_lm1_old_or_data`）

**厳密な残差**: `CendTwoLiveSecondLinesRefuted`
```
∀ first second, cost first = 1 → ¬CendAllNoForward second → ¬Correct [first, .pe second]
```
`cendLowerBound_three_iff_liveSecondLines` で下限3と同値。

**重大的な発見（REPORT.md §1.3 の値議論は不十分）**:
- OMR マスク書き込みは `newFlags = output.flags`（ALU のフラグビット）を格納するため、
  **1行目が任意のフラグパターンを植えられる**。2行目が `.entry` マスクを使うと
  **半マスク（0xffff0000 / 0x0000ffff）が到達可能**になる
- `value_closure.py` を cendWitness で再実行: 1段目 V1(385)・L(190) は目標半分を避けるが、
  **2段目 W2(57,740) は `0x08074181`（high16=0x0807）と `0x00000605`（low16=0x0605）を含む**
  — 目標高語 `0x08070605` の両半分が別々に存在する
- `cendMixWords (L ∪ W2)` は両目標語を含むと証明可能

→ **「2行では不可能」の経験的根拠が崩れた**。2行目の「マスクフラグと必要なレーン語を
同一行で両立できるか」という**共同到達性**の議論が必要で、値閉包では足りない。

**行動**: 2行解の有界探索を実測で実行中（マスク植え付け + 半マスク組み立て）。
見つかれば convert-endian の最小は3ではなく2になり、問題の性格が変わる。

## convert-endian: 2行解の探索で**見つからず**、最小3語が再確認される

`research/experiments/cend2-search/`。公式 judge でベースライン再確認: `ACCEPTED score=3`。

**半マスク懸念は実在するが、データが障害**:
- プローブ `sdec $m0v $omr1` は PE/サイクルごとに半マスクニブルを植える
- 2行候補 `sdec $m0v $omr1` + `sbsl $m[0,1,0,1] $aluf …/$imr1` は実際に別サイクルから
  LM1[0]=0x5FE13DB3 を組み立てる（半マスク commit は機能する）
- しかし**データが目標にならない**

**網羅探索（`search2.rs`、mncore_sim の意味論を移植）**:
- 1行目: 17演算 × S/I/L × 54ソースチャネル → `$omr1` 書き込み
- 2行目: 17演算 × S/I/L × 522チャネル、宛先4種 × マスク有無、マスクニブル = 1行目のフラグ
- 結果: **found=0、safe_lane_matches=0、best_lanes_in_one_config=0**
- 非空性対照 `--identity`（目標=入力半分）では found=645、37,513,068 レーン一致 → 探索は空虚でない

**imm 経路は反証**: 1行目=imm はフラグ0なので全面書き込みのみ。17演算×S/I/L、両オペランド順、
16bit 全 2^16 定数、32bit 代数的+全シフト、64bit 両エンコーディング → 0解。
さらに2行目は1行目の imm を GRF 経由で読めない（hazard checker が `DataRaceError`）。`$aluf` のみ無料で渡る。

**証人の詳細**: `ibsr $m1v $m1v` + `sxor $peid $aluf` は PE2 で目標語 0x08070605 を1バス語に作るが、
1行目のフラグが 0x3 なのでマスクが誤語を選び、PE0 では 0x08050607 になる。
→ 残差は**値の到達性ではなく、マスクと値の共同整列**。

**構造的障害**: 目標語0は `[bswap16(w1.lo) が上位, bswap16(w1.hi) が下位]`（半分が入れ替わる）。
16bit 演算はレーン単位で、唯一のレーン交換は 16 の回転/シフトだが、非転送オペランドに 16 が無い。
2行目がシフト16を転送で受けても x が未交換で、バイト交換にならない。

**未探索**: MAU（自然な fv/hv は screening 済み、要素単位でレーン交換なし）、msl/msr（フラグ常0）、
bfe/bfn、matrix/L1BM/L2BM/mv、複数宛先、flush マスク、mask/maskn 指令
（指令マスクは行頭でラッチされるので、`$omr1` を書き自身の LM1 書き込みを自己マスクする行は何も書かない）。

→ **最小3語は維持**。Lean 側の残差 `CendTwoLiveSecondLinesRefuted` は
「共同整列」の義務として残る。

## **モデルギャップの発見**: Lean の機械はアセンブラのハザード規則を検査しない

`ProofsLean/CendTwoLinesJoint.lean`（856行）を配線。ルート 948 jobs。

**発見**: `cendSealedMachine.step = executeNormalizedLine` は `.pe` で
`executeIntegerProducerInstructionLine` を呼ぶが、これは**ハザードチェッカーを参照しない**
（見るのは `checkParsedTopLine` = issue/SDM 3.6.4、wait タグ、未対応行のみ）。
`checkParsedTopLine` は1行しか見ないので、**行間の RAW 距離は検査されない**。

検証: `imm i"0x00080008" $r0v` → `sbsl $m0v $r0v $n[1,0,3,2]`（2行目が1行目の GRF r0 を読む）は
ネイティブモデルで実行でき PE0 LM1[0] = `0xeacbb33de15f66dc` になるが、
公式 judge は `DataRaceError` で拒否する（`research/experiments/cend2-search/MODEL-GAP.md`）。

**帰結**:
- `CendTwoLiveSecondLinesRefuted` は**探索より厳密に広い空間**を量化する。`found=0` は含意しない
- 逆に、Lean で**広い空間**について下限を証明できれば、judge が受理する狭い空間については
  **アプリオリに成立**する（下限は保守的）
- したがってモデルギャップは下限にとって安全側だが、証明の対象が広いぶん難しい

**推奨**: (i) 拡大された空間について shape を証明する、または
(ii) 受理される前にアセンブラのハザード正当性をモデルに含める、のどちらかを選んでから
`LowerBound 3` を主張する。

### 証明済み（`CendTwoLineCommitShape` を仮定）
- **共同マージ代数**: `CendSelectedHalfSafe`（マスクが選ぶ半分がデータの目標半分でない）+
  `mergeSelectedWord_ne_target_of_selectedHalfSafe`
- **共同 commit 連鎖定理**: `commitParsedMaskedWrites_lm1_ne_target_of_selectedHalfSafe`
  — 任意の準備リストについて、per-write の共同安全性から観測語が目標から離れることを証明
- 2段の合成 `cendTwoCommitChains_ne_target`
- 近接打の形式化（`0x3` ニブルは**語1**を選び語0を残す = 誤語 commit、PE0 バス `0x08050607`）
- 証人での1段値集合のカーネル検査（34秒の `decide`）: 1段の半混合はどちらの目標語にもならない
- `cendLowerBound_three_of_commitShape (peLines) (shape) : LowerBound … 3`

**残り**: `CendTwoLineCommitShape` の2つの合接項 —
(1) 任意（非 plain）族の準備リストへの commit 分解、(2) 2行目の per-write 共同安全性
（データが1行目の転送由来なので2段）。

## 要件との照合: ハザードは現状モデル化されていない（重要）

ユーザ要件は「下限は全ISA・全実行経路・全入力・初期状態・**ハザード**を扱う」。
現状の `wholeMachine` / `cendSealedMachine` は `checkParsedTopLine`（issue/SDM 3.6.4、
wait タグ、未対応行）のみで、**アセンブラのハザード規則（行間 RAW 距離）を検査しない**。

したがって現状の下限は「ハザード規則を無視した、より広いプログラム空間」についての定理である。
これは下限としては**保守的**（judge が受理する狭い空間にはアプリオリに成立）だが、
要件の文言とは一致していない。

**選択肢**:
1. 現状のまま「ハザード規則を含まないモデルでの下限」と明示して報告する（保守的だが要件とずれる）
2. モデルに `assemble3` のハザード検査を組み込む（`viz/core` の hazard 実装を移植）
3. 両方: 現状の定理を残しつつ、ハザード付きモデル版を別途証明する

→ **未決**。次のラウンドで方針を決める必要がある。

## 訂正: ハザードは既にモデル化されている（要件は満たしている）

前ラウンドで「モデルはハザードを検査しない」と記録したが、**これは内側の
`executeIntegerProducerInstructionLine` だけを見た誤り**。外側の
`executeHazardAwareNormalizedLineCore`（WholeMachineStep.lean:7842-7875）は以下を検査する:

```
checkParsedTopLine instruction.toParsed          -- issue / SDM 3.6.4
parsedNormalizedLinePEAddressModesValid line     -- アドレスモード
parsedNormalizedLinePEHazardEvents? state.machine line  -- PE ハザード事象
HazardTrace.parsedLineBlockHazardEvents line.toParsed state.machine.hazardClock
(∀ pe < 4096, parsedPEHazardViolated (state.peHistory pe) currentPEEvents[pe])  -- PE ハザード
parsedBlockHazardViolated state.blockHistory currentBlockEvents                 -- ブロックハザード
```
さらに `stalledPEIssue`、wait タグ、pending MV の処理。

**したがって `wholeMachine` は PE ハザードとブロックハザードを履歴付きで検査しており、
要件「ハザードを扱う」は満たしている。**

**唯一モデル化されていないもの**: アセンブラ（`assemble3`）の**静的な**テキスト検査
（`DataRaceError` 等）。これは実行意味論の性質ではなく、**プログラムが存在するかどうかの
フィルタ**（テキストが棄却されればプログラム自体が無い）。

**帰結**: モデルのプログラム空間（`InstructionLine` のリスト）は、アセンブラが受理したテキストより
**広い**。したがってこの空間での下限は、受理されたプログラムについて**アプリオリに成立**する
（保守的）。要件との照合で問題は無い。

**記録の訂正**: 前ラウンドの「ハザード未モデル化」という記述は撤回。

## convert-endian の上限は「実行器リンク」で止まる（全問題共通の真のボトルネック）

`ProofsLean/CendAnswerCorrect.lean`（469行）を配線。ルート 949 jobs。

**`Correct cendSealedMachine cendSpec cendAnswer` は未証明**。理由:

`executeNormalizedLine` を3行について記号実行する必要があるが、その遷移は
issue 検査 → 4096-PE walk → 整数4サイクル準備（約100分岐のラダー）→ float-MAU 段 →
forwarding 更新 → マスク付き commit（`[1,0,3,2]` セレクタ）→ LM1 word 0/1 の読み出し、と長い。
ツリーにはこの3行についてこれを計算する補題が**存在しない**。
既存の `ConvertEndian` の補題は**手書きのデータパスモデル**（`ibsl`/`packedSingleFma`/
`sbslWithShift`/`selector2103`）であって `executeNormalizedLine` の還元ではない。

**証明済み（上限側の周辺）**:
- `cendAnswer`（3行）と `cendAnswer_score = 3`
- **受理**: 3行すべて `LegalParsedLine`、`checkParsedTopLine = true`、
  実行器の4前検査（受理・wait なし・未対応 ALU なし・全 producer 対応）すべて真
- `CendAnswerExecutorLink := Correct …` を named obligation として明示
- `cendOptimal : Correct → CendPELinesRefuted → CendTwoLineCommitShape → Optimal`
- `#print axioms` は全定理で標準3公理のみ（**ネイティブ公理を継承しない**）

**既存のネイティブ公理**（`ConvertEndian.answerDatapath_is_byteSwap._native.bv_decide`）を継承する
定理を列挙: `answerDatapath_is_byteSwap`、`answerDatapath_involutive`、
`answerProgram_eq_answerDatapath`、`answerProgram_parsed_second_line_readback`、
`answerMemoryCycle_readback`、`answerMemoryCycle_byteSwap`、`abstractConvertEndian_is_byteSwap`。
`integerAlu_ibsl_matches` / `integerAlu_sbsl_matches` はそれぞれ独自の公理を持つ。

### **真のボトルネックの同定**

Welcome が2行についてこの実行器リンクを確立するのに約50ラウンドを要した。
残り24問はすべて同じ壁を持つ。**問題ごとの「答えを `executeNormalizedLine` に接続する」
汎用の行実行代数が、プロジェクト全体の律速**である。

推奨される次の一手:
1. `StageCommitSpecific.executeIntegerProducerLineAtPECore_peRegisters_commit_list` を土台に、
   **行の実行結果を記号的に与える汎用補題**（`WelcomeOptimal.welcome_executeIntegerProducerInstructionLine_peRegisters`
   の一般版）を作る
2. float-MAU 段の commit と MAU スロット出力の同定
3. `.alu .bsl (some .s)` の準備とマスク付き LM1 書き込み + 読み出し
4. `answerDatapath` ↔ `byteSwap64Kernel` の公理なし同値

## **行実行代数が完成**（`LineExec.lean`、1750行）— 全問題共通の律速を解消

ルート 950 jobs。

**閉じた項目 1-4**:
1. `executeIntegerProducerLineAtPECore_peRegisters_eq` — 整数準備式と float 段の結果と float commit を
   **両方明示**し、`next.peRegisters pe = commit (intWrites ++ floatWrites)`
2. `executeIntegerProducerLineAtPEs_peRegisters_eq` — walk（4096 PE）の効果
3. **`executeNormalizedLine_pe_registers`** — 行レベルの文
4. **`executeNormalizedLine_pe_forwardingSlots`** — 次行の `$aluf`/`$mauf` 読みを計算可能にする
   （`linePreparedSlots`/`lineIssuedSlots` を新規定義）

**重要な訂正**: 「他の PE ファイルは不変」は**偽**。レジスタを書く行は**訪問した各 PE** に
その PE 自身の状態依存リストを commit する。証明したのは (a) 各 p での commit、
(b) 未訪問 PE は不変、(c) 非レジスタ成分は不変。

**項目 5（2行への特殊化）は1つの明示的 lowering 仮説付きで閉鎖**:
- `executeNormalizedLine_pe_aluf_read`（**無条件**）— 1行目が ALU producer を持ち `noforward` が無ければ、
  2行目の `$aluf` 読みは1行目の準備スロットから計算できる
- `immediate_prepareParsedIntegerALUExprCycles` — `imm` 行の4サイクル準備
- `executeNormalizedLine_immediate_aluf_read` — `imm` 行後の `$aluf` 値

**残る配管（数学ではない）**: `prepareParsedIntegerMatrixReadLineExpressions` の
**単一要素 fold** を Lean で閉じる。目標内の `match` の discriminant を書き換えると
"did not find an occurrence of the pattern" で失敗する。
`generalize` で scrutinee を一般化するか、`cases` しやすい形で fold を述べ直せば閉じる。
サイクルレベルの計算は証明済み。

**再利用可能な部品**: `parsedExprIsLineExecRow` + 12の事実、`lineExecRow_stage_identities`、
`executeIntegerProducerInstructionLine_pe_lineExec{,_exists,_frame}`、
`executeIntegerProducerLineAtPEs_peRegisters_commit_all` など。

## convert-endian の上限: 1行目の整数段が完全に計算される

`ProofsLean/CendAnswerExec.lean`（ビルド成功、標準3公理のみ）。

**閉じたもの**:
1. **単一要素 fold の残差** `prepareParsedIntegerMatrixReadLineExpressions_singleton`。
   前担当のヒントは不要で、`simp only [prepareParsedIntegerMatrixReadLineExpressions]` → `rw [prepared]` で直接通る。
   本当の罠は「式をレコードリテラルに書き換えると discriminant が stuck projection になる」こと
   （`cendImmExpr.normalize.toParsed` を残し `expression.op` だけ書き換える）
2. `executeNormalizedLine_immediate_aluf_read` の仮説を**解消**。`cendLine1_aluf` は無条件:
   PE0 の全 `.alu` スロットが `known ⟨0x34F80010 ++ 0x34F80010, same⟩`
3. **1行目の整数段を厳密に計算**: `cendImmWrites = [immWrite 0, aluWrite, immWrite 1, aluWrite, …]`。
   `cendImm_lowered`・`cendImm_prepared`・`cendImm_aluCycles`・`cendImm_rowExpression`・`cendImm_lineCycles` は**仮説なし**
4. `CendAnswerExecResidual`（`line1` と `tail` の2フィールド）と、そこから
   `cendAnswerCorrect_of_residual` / `cendOptimal_of_residual r peLines shape : Optimal ...` へ繋ぐ
   `cendAnswerCorrect_of_residual` / `cendOptimal_of_residual r peLines shape : Optimal ...`

**残り**:
A. 1行目の walk 成功 — `$r0v` は直接のマスクなし GRF0 宛先なので
   `toDirectMemoryDestination? cendR0 pe cycle bar0 bar1 tWord = some ⟨grf0, .word, ⟨cycle.val⟩⟩` が
   **全 pe/bar0/bar1/tWord** で成り立つ（現在は pe=0/bar=0 のみ）。これで各行の core step が `.ok` になり、
   4096-PE walk には「未訪問 PE は初期ファイル・forwardingValid=false・matrixRegisters 不変」の不変量が要る
B. 2行目（`ibsl` = 転送された即値による `.word` rotl16、`fvfma` が MAU バス `0x34F80018++0x34F80018`）、
   3行目（`sbsl` が MAU バスで halfword rotl8、宛先セレクタ `[1,0,3,2]` → LM1 word `[1,0,3,2][c] = byteSwap32(LM0 word c)`）、
   読み戻し words 0/1 = `byteSwap64 input`。**`ByteSwapKernel`（公理なし）を使う**こと

## convert-endian 上限: 1行目の per-PE core step まで完了、walk と2-3行目が残り

`ProofsLean/CendAnswerExec.lean`（986行）を配線。ルート 951 jobs。

**閉じたもの**: 単一要素 fold、PE 非依存の lowering/destination/selection（全 pe/BAR/T）、
`cendLine1_aluf`（無条件）、`cendImm_pecore`（**任意の PE** で core step が成功し commit が `cendImmWrites`）、
`executeParsedFloatMAUsAtPE_empty`、`CendAnswerExecResidual` → `Correct` / `Optimal` の組み立て。

**残り**:
- 1行目の **4096-PE walk**（frame 事実 + `finRange 4096` 帰納 + BAR テスト）
- 2行目・3行目（`ibsl` の rotl16、`fvfma` の MAU バス `0x34F80018++0x34F80018`、
  `sbsl` の halfword rotl8 とセレクタ `[1,0,3,2]`、読み戻し）

**2つの罠（記録）**:
1. `LineExec.executeIntegerProducerLineAtPECore_peRegisters_eq` は1行目には**使えない** —
   `floatWrites` が存在量化されたままで、float フィルタが空でも `floatFiles` しか固定されない。
   `cendImm_pecore` は core step を2つの match scrutinee で `cases` してやり直している
2. `decide` は自由変数を含むゴールで失敗する（"Expected type must not contain free variables"）。
   PE 非依存の lowering は `simp` + `Width.words`/`Bank.capacity`/`Nat.mod_eq_of_lt` で閉じた

## convert-endian の値連鎖が完全に計算される（`CendTail.lean`、600行）

ルート 953 jobs。

**無条件で計算**:
1. `ibsl $m0v $aluf $r8v` — 転送即値の count = `0x34F80010 % 64 = 16` で `.word` rotl16。
   `cendIbslWrittenWord w = w.rotateLeft 16`、`rotateLeft16_low/high`（16bit 半分が交換される）
2. `fvfma $aluf $aluf $aluf $s0v` — `cendMauShiftWord : singleFma 0x34F80010³ = 0x34F80018`（`decide`）、
   `cendMauShiftBus = 0x34F80018 ++ 0x34F80018`
3. `sbsl $aluf $mauf $n[1,0,3,2]` — 各 MAU halfword レーンの count が 24（= rotl8）で
   `cendSbslData w = byteSwap32 w`、宛先 c→[1,0,3,2]、
   `cendSbslLm1_readPair : readPair .lm1 … 0 = data 1 ++ data 0`
4. **`byteSwap64_eq_byteSwap32_halves`** — `ByteSwapKernel.byteSwap64Kernel` からバイト厳密に証明
   （`answerDatapath_is_byteSwap` と `bv_decide` は**不使用**）

**組み立て**: `cendTail_of_computation`、`cendAnswerExecResidual_of_line1_and_tail`、
`cendAnswerCorrect_of_tail : Correct cendSealedMachine cendSpec cendAnswer`。

**残差**: `CendTailComputation input s1`（Type 値、中間 State を運ぶ）—
`line1 : CendLine1Facts`（LM0 word 0/1 = 入力、BAR0=BAR1=0）、
`line2`/`line3` の `executeNormalizedLine` 成功、`afterTwo` の `.alu`/`.mau` スロット、
BAR/LM0 の frame、`afterThree` の LM1 = `cendSbslLm1 …`。
これは1行目の walk と同じ種類の作業（4096-PE walk + per-cycle 準備 + commit）で、値レベルの仮定は無い。

## 10度目の偽命題: `CendTailComputation.mauSlots` は偽

float-MAU のサイクルは常に `⟨output, 0⟩` を返す（下位が零）ため、転送される MAU ペイロードは
`⟨fmaWord ++ fmaWord, 0⟩` であって `cendMauShiftBus = ⟨fmaWord ++ fmaWord, fmaWord ++ fmaWord⟩` ではない。
`CendTailExec.cendMauShiftBus_ne_forward` で機械検証。`mauSlots` を主張する構造は** inhabit 不能**。

**値連鎖は無傷**: `IntegerALU.evaluateBus` は MAU バスの**高位半分しか使わない**ので、
`cendSbslData_forward` で実バスに対して `cendSbslData` が再証明される。
`mauSlots` は `cendTail_of_computation` のどこでも使われておらず、必要なのは `afterThreeLm1` だけ。

**修復版** `CendTailComputationForward`（`mauSlots : .known cendMauForwardBus`）と、
そこからの組み立て `cendTail_of_forwardComputation` / `cendAnswerCorrect_of_forwardTail` /
`cendAnswerCorrect_of_forwardResidual` を証明。

**残差** `CendTailForwardResidual` — 2行・3行の 4096-PE walk、per-cycle の `ibsl`/`sbsl` 整数準備、
`fvfma` の float 段（1行目の存在は `cendAnswerExecResidual_line1` で既に無条件）。

**補助（全て証明済み）**: `$m0v`/`$r8v`/`$n[1,0,3,2]`/`$s0v` の任意 PE/cycle/BAR での厳密な lowering
（`cendM0_access` 等）、`cendFma_lowered`、`cendFmaBusValue`、実バス上の `sbsl` データパス。

**教訓（10度目）**: 「MAU バスの下位も値が入っている」という直感が再び誤り。
`executeParsedFloatMAUCycleAtPE` は `⟨output, 0⟩` を返す。値は高位のみ。

## convert-endian 上限の現在地: `CendTailForwardResidual` まで

`CendTailExec.lean`（405行）を配線。ルート 954 jobs。

**無条件で閉じたもの**:
- `cendLine1Files_of_execution` — 1行目の実行後の PE0 レジスタファイルが `cendLine1Files input` に一致
  （BAR の2等式のみ未証明。walk レベルの context frame が必要で、4M heartbeat でタイムアウトしたため保留）
- `CendTailComputationForward`（`mauSlots : .known ⟨fmaWord++fmaWord, 0⟩`）の**値連鎖組み立て全体**
- `cendAnswerCorrect_of_forwardTail` / `cendAnswerCorrect_of_forwardResidual`
- 補助: `cendFmaCycle`、`cendFma_lowered`、`linePreparedSlots_mau`、`cendSbslData_forward`、
  `cendM0_access` / `cendR8_access` / `cendN2103_access` / `cendS0_access`（任意 PE/cycle/BAR の厳密 lowering）

**元の `CendTailComputation` は inhabit 不能**（`mauSlots` が偽）。推奨修正は
`cendMauShiftBus := ⟨fmaWord ++ fmaWord, 0#64⟩` と `cendMauShiftBus_eq` の更新、
`cendSbslData` の証明は `CendTailExec.cendSbslData_forward` で代替。
**現状は未修正のまま残す**（`CendTail.lean` は証明済みで、この構造を inhabit しようとしない限り無害）。

**残差** `CendTailForwardResidual`: 2行・3行の `executeNormalizedLine` 成功（walk）、
`aluSlots`（2行目整数段）、`mauSlots`（2行目 float 段、真の値）、
`afterTwoBar0/Bar1/Lm0`、`afterThreeLm1`（3行目 LM1 commit）。
