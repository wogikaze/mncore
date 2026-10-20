# lowerbound: working notes

Deliverable: **`research/preliminary/fizzbuzz-delivery/README.md`**.

Result:
- **8 assembled words** are necessary and sufficient for the final delivery of
  the 4096-long-word FizzBuzz block from PE-side storage to Group 0 DRAM
  (tight: lines 86–93 of the accepted 93-word solution; `vsm/delivery_tail.vsm`
  assembles to j=6,m=2).
- **9 words** are necessary for any complete FizzBuzz program (full ISA):
  one producer word + the 8-word delivery.  A 9-word program attains this for a
  constant block (`nine_word.vsm`); the accepted FizzBuzz solution uses 10
  words for producer+delivery because it reads GRF and needs one forced nop.
- **Target 1 is vacuous:** one MV word writes at most 16384 long words =
  131072 bytes to Group 0 DRAM (`mvp/n16384`; `n=32768` is rejected by the
  assembler), so `ceil(32766/131072) = 1`.  The binding hop is L1BM→L2BM
  (`l2bmd` moves 2048 long words = 16384 bytes per word).

Evidence:
- `research/preliminary/fizzbuzz-delivery/delivery_model.py` — BFS + brute force + CP-SAT;
  `K=7 INFEASIBLE`, `K=8 OPTIMAL`.
- `research/preliminary/fizzbuzz-delivery/probe_isa.py` — assembler probes (n limit, hazard gaps).
- `research/preliminary/fizzbuzz-delivery/logs/` — exact outputs, including:
  - `one_l2bmd.txt`: deleting one `l2bmd` gives **2048 mismatches** (one
    `l2bmd` moves exactly 2048 words);
  - `mvp16384.txt`: one `mvp/n16384` writes 16384 long words;
  - `nine_word.txt`: 9-word constant delivery;
  - `fbverify_answer.txt`: accepted baseline `score=93 j=91 m=2`;
  - `aluf_92.txt`: the 92-word `$aluf` shortcut is a negative result
    (4096/4096 mismatches).
- `research/preliminary/fizzbuzz-delivery/verify.sh` — reproduces everything, ends with
  `ALL VERIFICATION STEPS PASSED`.

Working scripts kept here: `probe*.py`, `run_official.py`, `l1bm_probe*.py`,
`sameword_probe.py`, `mvd_probe.py`, `nine_word.vsm`, `cand_*.vsm`.  The
deliverable copies are under `research/preliminary/fizzbuzz-delivery/`.
