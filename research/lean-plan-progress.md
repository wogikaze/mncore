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
