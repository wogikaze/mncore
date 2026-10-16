# SDM 3.6.4 issue-rule audit

This is a source-level comparison of the manual section
`docs/mncore_llm/chapters/ch03/section-3.6.4__並列実行条件__66b35ffe.md`
with `viz/core/src/issue.rs` and its Lean mirror in
`ProofsLean/Issue.lean`. It records what the current checker models and where
it is narrower than, or does not model, the manual. Passing this audit is not
proof that `assemble3` accepts every modeled line.

| SDM condition | Current implementation | Status for exhaustive enumeration |
| --- | --- | --- |
| At most one expression in each issue group | Rust and Lean group uniqueness checks | Partial: `l2bmdars` has a special assembler exception with another L2BM group, but the checker assigns it the ordinary L2BM group and rejects that case. This omits potentially legal lines. |
| `nop` may issue only with `wait` | `ParsedLine` represents nop as a separate top-level line; `LegalParsedLine` checks only PE expression lists | Not connected at the top-level line/parser boundary. |
| At most two MAU groups, same precision | Rust and Lean count calculation, matrix-write, and matrix-read groups and compare precision | Mirrored for represented expression records. |
| Vector FMA/MUL plus matrix write input agreement | Rust and Lean compare the structured operand at source 2 against the matrix-write source | Mirrored for structured operands; parser correspondence is still open. |
| Each matrix register side appears at most once | Rust and Lean count X/Y matrix operands in sources and destinations | Mirrored for represented matrix operands. |
| No two expressions write the same PE operand | Issue projection's write list contains only `.mem` operands; matrix uses are counted separately | Incomplete: OMR and other destination forms are not part of the general write-conflict check. |
| Reads from one PE operand use one region, including mask-flag reads | Read projection contains only `.mem` source operands | Incomplete: mask and forwarding reads are not explicitly projected into port constraints. |
| LM0/LM1 read/write regions agree | Rust and Lean compare projected `.mem` accesses | Mirrored for projected accesses only. |
| Immediate excludes LM0 access | Rust and Lean check projected `.mem` accesses | Mirrored for projected accesses only. |
| At most one zero-flush mask | Rust and Lean count expressions with a flush | Mirrored for parser-produced flush metadata. |

The current checker can reject the `l2bmdars` exception and can miss conflicts
involving operands outside its PE-memory projection. The first gap can omit
legal candidates; the latter can admit lines the assembler rejects. The
top-level nop restriction also needs to be connected to parsed source lines.
These gaps must be resolved against the manual and `assemble3` before
promoting `parallel_issue_and_memory_port_legality` beyond
`partial_datapath_only` in `coverage.json`.

The boundary evidence now includes seven valid-operand pairs of `l2bmdars` with
`l2bmb`, `l2bmb2`, `l2bmd`, `l2bm@`, `l2bmr*`, `l2bmr2*`, and `l2bmi`; all
seven were rejected by `assemble3`. This does not identify the manual's special
condition, so it does not justify removing the completeness gap. The
`l2bmdars; l2bmdarw` pair remains accepted and is separately recorded.

## Next formalization work

1. Model the `l2bmdars` simultaneous-issue exception explicitly, or establish
   from the challenge submission contract that it cannot occur in candidate source.
2. Project every PE-operand read and write class required by the manual,
   including masks and fixed destinations, then add cross-expression port checks.
3. Connect top-level line parsing, nop/wait combinations, and PE expression
   checking; compare boundary combinations with `assemble3`.
4. Prove parser-to-projection correspondence before using the predicate in
   `MNCore.machine`.
