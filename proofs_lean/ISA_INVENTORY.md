# MN-Core 2 ISA inventory (source-derived, not an ISA completeness proof)

This inventory records the instruction and operand model present in this repository.
It is derived from `mncompile/machine.py` and `viz/core/src/vsm.rs`; the assembler
manual remains authoritative. The compiler parser and simulator do not claim to
accept/model every legal hardware encoding. `proofs_lean/coverage.json` therefore
continues to mark exhaustive ISA coverage and full semantics as unproven.

## Opcode families

- **ALU**: `zero`, `imm`, `immu`, plus typed ALU names generated from `ALU_OPS` and
  `ALU_PRECISIONS` in `mncompile/machine.py`. Operations include `msl`, `msr`,
  `passa`, inc/dec, not/lnot, rsqrt/floor/ftoi, bfe/bfn, max/min/packbit,
  and/or/xor/add/sub, lsl/lsr/bsl/bsr, relu variants and lrelu variants. Integer
  signedness prefixes are generated only where `UNSIGNED_OK` allows them. `hbfe`
  and `hbfn` have mantissa arguments `/6` through `/9`.
- **MAU**: precision `d/f/g/h`, vector or matrix mode, and fma/mul/add/passa
  forms subject to the generator's restrictions; `d` fma/mul have `u`/`d` half
  variants, and `d`/`h` support rounding suffix `r`. Matrix transfers are
  `dmwrite/dmread`, `fmwrite/fmread`, `gmwrite/gmread`, `hmwrite/hmread`.
- **Other PE expressions**: `l1bm*`, `l2bm*` (including `l2bmdarw`), `mv*`,
  `wait`, `noforward`, and `nop`. Detailed spelling/operand acceptance is in
  `parse_expr`, `n_inputs`, and the corresponding `L1Op`, `L2Op` and `Op` enums;
  it is not restated as a claim of all legal hardware spellings here.

## Operand families represented by the parser/model

- PE memory: LM0, LM1, GRF0, GRF1 and T; word widths 1/2/4; address schedules,
  negation, precision extension/rounding, T-indirect and MADPE modifiers, and
  write masks.
- Forwarding (`aluf`, `mauf`, `lbf`, `mreadf`), fixed IDs (`l2bid`, `l1bid`,
  `mabid`, `peid`, `subpeid`, `msb1`), immediates, `$zero`, `$nowrite`, OMR
  destinations, BAR operands and matrix registers.
- Block/memory transfer operands: L1BM, L2BM, DRAM/DAR, PDM and matrix X/Y
  operands. The model also has raw operands for instruction forms not simulated.
- Masks: fixed four-cycle patterns or OMR entries 1–15, with long (`ll`) form.

This is a model-family summary. Numeric ranges, combinations, alignment and
instruction-specific restrictions must be checked against the parsers and the
manual; a family appearing here does not prove every combination legal.

## Same-step issue checks implemented in `viz/core/src/issue.rs`

- At most one expression per issue group: ALU, MAU calculation, matrix write,
  matrix read, L1BM (turnaround is operand-sensitive), L2BM, L2BM DAR write,
  wait, and noforward. MV and unrecognized `Other` expressions are not assigned
  a simulated group by this checker.
- At most two of MAU calculation/matrix-write/matrix-read per step; if two,
  precision must match. For vector FMA/MUL paired with matrix write, the vector
  operation's second input must equal the matrix-write input.
- Each matrix register side X/Y occurs at most once. Each PE memory has at most
  one writer and all reads of that memory use the same region. LM0/LM1 read and
  write regions must agree. Immediate instructions cannot share a step with an
  LM0 access. At most one zero-flush mask is applied per step.

These are the checker predicates currently mirrored in `ProofsLean/Issue.lean`;
they do not establish complete assembler legality, all memory-port rules, or
hardware behavior for unmodeled instruction families.
