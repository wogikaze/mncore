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
| `nop` may issue only with `wait` | `ParsedLine`/`InstructionLine` use a dedicated nop-with-optional-wait constructor; PE and MV rows are distinct constructors | Shape and local checker are connected for normalized `InstructionLine`; source parser correspondence and whole-program legality remain open. |
| At most two MAU groups, same precision | Rust and Lean count calculation, matrix-write, and matrix-read groups and compare precision | Mirrored for represented expression records. |
| Vector FMA/MUL plus matrix write input agreement | Rust and Lean compare the structured operand at source 2 against the matrix-write source | Mirrored for structured operands; parser correspondence is still open. |
| Each matrix register side appears at most once | Rust and Lean count X/Y matrix operands in sources and destinations | Mirrored for represented matrix operands. |
| No two expressions write the same PE operand | PE-memory/BAR bank outputs, OMR writes, and implicit `$lbf` writes have separate uniqueness checks | `$lbf` writes from normal and turnaround L1BM groups and shared LM0/LM1 output banks (including `$mb`/`$nb`) are modeled; broader assembler/parser correspondence remains open. |
| Reads from one PE operand use one region, including mask-flag reads | Ordinary PE-memory reads compare bank and region; mask reads separately require one width and one variable OMR entry; BAR writes exclude reads from their LM bank | Memory and mask ports are mirrored; forwarding operands are fixed-region read-only values and can repeat. `$mreadf` is separately restricted to source 0 of ALU expressions, matching SDM 3.6.1.18. Parser correspondence remains open. |
| LM0/LM1 read/write regions agree | Rust and Lean compare projected `.mem` accesses | Mirrored for projected accesses only. |
| Immediate excludes LM0 access | Rust and Lean check projected `.mem` accesses | Mirrored for projected accesses only. |
| At most one zero-flush mask | Rust and Lean count expressions with a flush | Mirrored for parser-produced flush metadata. |

SDM 3.6.1.19 additionally requires `$nowrite` to be the sole destination of
its expression. The checker now enforces that condition and rejects duplicate
destinations within one PE-memory bank, matching the sampled `assemble3`
rejections for `$nowrite`, `$nowrite` mixed with another output, and duplicate
LM0 outputs. These output-shape checks supplement the inter-expression port
rules above.

SDM 3.6.1.7 and 3.6.1.9 identify `$mb` and `$nb` as LM0/LM1 base-address
registers. Their destinations share the corresponding LM output bank, and a
base-address write cannot issue with a read from that same bank. The checker
models both constraints; selected accepted and rejected combinations are
recorded in `evidence/isa-bounds/reference.json`. This remains sampled
assembler evidence rather than a proof of full parser correspondence.

The current checker can reject the `l2bmdars` exception, which can omit legal
candidates. Other memory-port and operand-form conditions may remain outside
the checked projection and admit lines the assembler rejects. The top-level
nop restriction also needs to be connected to parsed source lines. These gaps
must be resolved against the manual and `assemble3` before
promoting `parallel_issue_and_memory_port_legality` beyond
`partial_datapath_only` in `coverage.json`.

The boundary evidence now includes seven valid-operand pairs of `l2bmdars` with
`l2bmb`, `l2bmb2`, `l2bmd`, `l2bm@`, `l2bmr*`, `l2bmr2*`, and `l2bmi`; all
seven were rejected by `assemble3`. A further matrix tested eight L2BM
operation classes with both `.0` and `.1` selectors; all 16 combinations were
also rejected. This does not identify the manual's special condition, so it
does not justify removing the completeness gap. The
`l2bmdars; l2bmdarw` pair remains accepted and is separately recorded.

For the other line-level cases, the assembler accepts `nop; wait i01`, rejects
`nop; iadd ...`, and rejects `mvp/...; iadd ...` and `iadd ...; mvp/...` in
the sampled valid forms. The zero-count nop/wait form is rejected as well.
This supports modeling nop-with-wait as a dedicated line constructor and MV
as a separate line form, while parser-to-assembler correspondence remains to
be proved.

`InstructionLine.toParsed` connects normalized PE/nop/MV lines to the
existing top-level issue checker. `InstructionLine.localIssueLegal` is
equivalent to that check, and the subtype that also satisfies the bounded
finite envelope has a finite carrier for every cost bound. This is only
line-local legality; it does not include cross-line hazards or prove that all
assembler-accepted source lines normalize into this subtype.

SDM 3.6.1.15–3.6.1.18 assign the forward producers as follows: ALU→`$aluf`,
MAU calculation→`$mauf`, L1BM-to-PE→`$lbf`, and matrix read→`$mreadf`.
Group uniqueness limits the ALU, MAU-calculation, and matrix-read producers;
the separate `$lbf` check covers the normal and turnaround L1BM groups together.
`$mreadf` is legal only as the first ALU source. The 84-case assembler-role
record includes accepted `iadd $mreadf ...`, rejected second-source use, and
rejected L1BM-reduction use. These are selected syntax probes, not a complete
operand parser proof.

The assembler accepts `gmfma ... $omr1` and `lpassa $lt $omr1` independently,
but rejects their simultaneous issue with an `out_maskreg` conflict. The pair
is also rejected when the destinations are `$omr1` and `$omr2`, which supports
a single OMR write port rather than entry equality. Rust and Lean now enforce
at most one OMR destination per PE issue line. Mask-selector reads are modeled
separately by requiring a common width and variable entry across the line. The
assembler accepts `lpassa .../$imr1` alongside a `gmfma` OMR write to either
entry 1 or entry 2, confirming that the OMR read and write ports are distinct.
Forwarding-register reads use a fixed temporal region and can be repeated, as
documented for `$mauf`. Implicit forwarding writes are checked for `$lbf`;
other output forwarding registers are separated by their producer issue groups.

## Next formalization work

1. Model the `l2bmdars` simultaneous-issue exception explicitly, or establish
   from the challenge submission contract that it cannot occur in candidate source.
2. Compare remaining PE-operand reads and writes with `assemble3`, including
   full parser-to-projection evidence for forwarding operands and producer mappings.
3. Connect top-level line parsing, nop/wait combinations, and PE expression
   checking; compare boundary combinations with `assemble3`.
4. Prove parser-to-projection correspondence before using the predicate in
   `MNCore.machine`.
