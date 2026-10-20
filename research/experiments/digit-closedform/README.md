# digit-closedform — T-chain elimination attempt

Goal: replace the 11-"ALU" chain that selects the decimal-digit range in the
93-word FizzBuzz answer (`problems/challenge/20.fizzbuzz/answer.vsm`).

**Headline results**

1. **The chain is 6 ALU + 6 MAU, not 11 ALU.**  The six `lsub` are ALU; the six
   `fvadd` are MAU.  The binding resource is the ALU issue group, so deleting
   the whole chain saves **6 ALU expressions**, not 11.  (`semantics.md` §1.)
2. **Exact semantics** (verified on all 4096 blocks):
   `k = #{i : r18 >= T_i(w)}`, `T = 2^23 + 2k`, with
   `w=s4`, `M=8w+39`, `n1=s0+C_w`, `C={2:8,3:13,4:66,5:599}`,
   `r18 = n1 mod M`, and
   `T_i = w+8, 2w+8, 3w+13, 4w+23, 5w+33, 6w+33`.
   See `semantics.md` §2 and `verify_chain.py`.
3. **No exact 3–5 ALU closed form found.**  The map `r18 -> k` is a w-dependent
   step function with 6 thresholds whose gaps are `w, w+5, w+10, w+10, w`.
   A residue table indexed by `r18>>3` is wrong for 3010/4096 blocks (r18 is
   reduced mod M, so `r18>>3` is not the residue).  A w-dependent 8-block table
   is still wrong for 1240/4096 blocks due to within-block splits, and needs
   40 table entries.  No affine / floor / difference-of-floors formula fits.
4. **Best VSM produced** (broken but lower word count):
   `cand_table_keep51.vsm` = **91 words, 2718 mismatches**, official assembler
   accepts it.  `cand_table.vsm` = 90 words, 3673 mismatches, but the official
   `assemble3` rejects it (exit -6), so it is not a legal candidate.
5. **L51 is live.**  `fftoi $lmt[18,18,16,16] $t` (line 51) writes an LM0 word
   that is *not* always overwritten (the canvas overwrite is masked), so
   deleting it gives 3673 mismatches.  This corrects an earlier guess.
6. The region comparisons `{0,32,408,4672}` cannot be folded into the chain
   output: they compute `w`, which is an **input** to the chain (and to
   `C_w`/`M`).  They are upstream, not redundant with k.

## Commands

```sh
cd research/experiments/digit-closedform
python3 collect_chain.py                 # 1.4 s, writes chain_data.csv
python3 verify_chain.py                  # 4096/4096, failures: none
python3 build_table_candidate.py         # writes cand_table.vsm
cd ../../..
python3 tools/fbcheck.py research/experiments/digit-closedform/cand_table_keep51.vsm
# -> FAIL words=91 mismatches=2718
python3 tools/fbverify.py research/experiments/digit-closedform/cand_table_keep51.vsm
# -> RESULT MISMATCH (assembles; output wrong)
cd research/experiments/digit-closedform
python3 analyze_candidate.py cand_table_keep51.vsm
```

## Files

See `semantics.md` §7.  The important ones:

* `semantics.md` — exact chain semantics, failed closed-form classes, evidence.
* `verify_chain.py` — the numerical proof over all 4096 blocks.
* `collect_chain.py`, `chain_data.csv` — per-block data at the chain boundary.
* `cand_table_keep51.vsm` / `cand_table.vsm` — lower-word broken candidates.
* `analyze_candidate.py` — which output words break and why.
