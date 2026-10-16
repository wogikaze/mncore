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
| No two expressions write the same PE operand | PE-memory ports are checked by memory bank; OMR writes have a separate single-write-port rule | OMR write conflicts are mirrored and checked against the assembler for same and different entries. Other fixed/forwarding destination conflicts remain incomplete. |
| Reads from one PE operand use one region, including mask-flag reads | Ordinary PE-memory reads compare bank and region; mask reads separately require one width and one variable OMR entry | Mask-flag read constraints are mirrored and assembler checked. Forwarding reads are not yet explicitly represented. |
| LM0/LM1 read/write regions agree | Rust and Lean compare projected `.mem` accesses | Mirrored for projected accesses only. |
| Immediate excludes LM0 access | Rust and Lean check projected `.mem` accesses | Mirrored for projected accesses only. |
| At most one zero-flush mask | Rust and Lean count expressions with a flush | Mirrored for parser-produced flush metadata. |

The current checker can reject the `l2bmdars` exception and can miss conflicts
involving operands outside its PE-memory, mask-read, and OMR-write projections. The first gap can omit
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

For the other line-level cases, the assembler accepts `nop; wait i01`, rejects
`nop; iadd ...`, and rejects `mvp/...; iadd ...` and `iadd ...; mvp/...` in
the sampled valid forms. The zero-count nop/wait form is rejected as well.
This supports modeling nop-with-wait as a dedicated line constructor and MV
as a separate line form, while parser-to-assembler correspondence remains to
be proved.

The assembler accepts `gmfma ... $omr1` and `lpassa $lt $omr1` independently,
but rejects their simultaneous issue with an `out_maskreg` conflict. The pair
is also rejected when the destinations are `$omr1` and `$omr2`, which supports
a single OMR write port rather than entry equality. Rust and Lean now enforce
at most one OMR destination per PE issue line. Mask-selector reads are modeled
separately by requiring a common width and variable entry across the line. The
assembler accepts `lpassa .../$imr1` alongside a `gmfma` OMR write to either
entry 1 or entry 2, confirming that the OMR read and write ports are distinct.
Forwarding-register reads and implicit forwarding writes remain outside the
general port projection.

## Next formalization work

1. Model the `l2bmdars` simultaneous-issue exception explicitly, or establish
   from the challenge submission contract that it cannot occur in candidate source.
2. Project every PE-operand read and write class required by the manual,
   including masks and fixed destinations, then add cross-expression port checks.
3. Connect top-level line parsing, nop/wait combinations, and PE expression
   checking; compare boundary combinations with `assemble3`.
4. Prove parser-to-projection correspondence before using the predicate in
   `MNCore.machine`.
