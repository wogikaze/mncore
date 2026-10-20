# RESULTS — automated superoptimization campaign (2026-10-20)

**Outcome: no improvement below 93 words was found.**  The campaign evaluated
**48,446 distinct programs** through the official assembler and
**17,402 of them through the native simulator** (all 4096 dumped long words
compared).  **20,247 candidates had 92 rows**, i.e. were intended to save one
word; 14,682 were rejected by the assembler, 3,325 ran and mismatched, 2,240
crashed at runtime, and **zero** were correct.  The best candidate remains the
93-word baseline (j=91, m=2), re-verified with `tools/fbverify.py`
(`ACCEPTED!! score=93 j=91 m=2 bytes=3054`).

This is a *local* negative result with a structural explanation (section 5),
not a failure to try: the transformation space cannot reach 52.

## 1. Scorer agreement with the official tools

From `harness/verify_agreement.py` → `logs/agreement.json`:

| check | result |
| --- | --- |
| `tools/fbcheck.py` on baseline | `OK words=93 lines=93 mismatches=0` |
| in-process scorer on baseline | same (93 words, 0 mismatches) |
| `tools/fbverify.py` on baseline | `ACCEPTED!! score=93 j=91 m=2 bytes=3054` |
| assembler vs simulator word count, 40 cached candidates | 40/40 equal |
| `fbverify` on 3 fast-scorer-accepted candidates | 3/3 `ACCEPTED`, score == words |

The official assembler is also the first scoring stage: an assembler error is
a hard reject (`tools/fbverify.py` cannot run without it), so the filter is
sound and does not admit candidates the gate would refuse.

## 2. Measured throughput

`harness/bench.py --n 40 --workers 0,8,10 --json logs/bench.json`
(worst-case set: every candidate assembles and is fully simulated; shared
12-core host, load ~4–14 from concurrent jobs):

| workers | candidates/s | simulator runs/s |
| ---: | ---: | ---: |
| 0 (serial) | 2.29 | 2.29 |
| 8 | 8.74 | 8.74 |
| 10 | 9.93 | 9.93 |

One simulator evaluation of a 93-line program costs ~0.45 s (93 steps × 4096
PEs, ~30 lines take the masked/slow path).  The official `assemble3`
pre-filter costs ~6 ms; it rejected 31,044 of the 48,446 candidates, so the
campaign aggregate is higher: the final run did **26.2 new candidates/s** and
**10.5 simulator runs/s** (`logs/summary-final.json`).  Serial in-process
scoring is 2.2–2.3/s; the SQLite cache replays at >50,000/s.

## 3. Campaign waves

| wave | submissions | new | simulated | accepted | accepted < 93 |
| --- | ---: | ---: | ---: | ---: | ---: |
| seed (baseline) | 3 | 1 | 1 | 3 | 0 |
| singles (delete, repair, merge, split, reorder, swap, relocate/8, move_row, commute, const, addr, noforward) | 5,116 | 1,017 | 554 | 119 | 0 |
| moves (every expression move + every row move into a compatible row) | 9,090 | 6,659 | 2,064 | 12 | 0 |
| dissolve (both expressions of every 2-expression row into two other rows, nearest 14 hosts) | 5,602 | 5,473 | 900 | 0 | 0 |
| finish (chained: dissolve the remaining expression of every partial-dissolution state) | 33,599 | 22,382 | 7,555 | 84 | 0 |
| repair_race (insert a nop at the assembler-reported data-race line of a 92-row move, then delete a nop) | 1,444 | 1,369 | 183 | 0 | 0 |
| plateau (beam/random walk over 48 word-neutral correct seeds, 4,000 samples) | 4,000 | — | — | — | 0 |

The `plateau` wave is the search loop proper: it keeps a pool of 93-word
simulator-correct states recovered from the cache (308 were available,
including partial dissolutions and row permutations), samples mutations from
the pool, and adds every new correct state back, so two-step dissolutions are
reachable.  It produced no candidate below 93 either.

`singles` includes the full one-step neighbourhood; `relocate` (8.5k
word-neutral row permutations) is sampled 1-in-8 because only its interaction
with the plateau matters.

## 4. Result distribution and failure modes

Simulator mismatch distribution over the 17,402 simulated candidates:

| mismatches | candidates |
| --- | ---: |
| 0 | 852 |
| 1–9 | 128 |
| 10–99 | 293 |
| 100–999 | 1,161 |
| 1000+ | 7,921 |

Programs by row count (= word count) and stage:

| rows | accepted | sim fail | sim error | asm error |
| ---: | ---: | ---: | ---: | ---: |
| 92 | **0** | 3,325 | 2,240 | 14,682 |
| 93 | 769 | 6,166 | 4,760 | 16,362 |
| 94 | 83 | 12 | 47 | 0 |

Assembler rejections by cause (`logs/final_report.json`):

| count | cause |
| ---: | --- |
| 10,438 | field conflict `mau`/`mau` (two MAU expressions in one row) |
| 5,039 | generic assembler abort (early campaign, before detailed capture) |
| 3,305 + 686 | field conflict `lm0`/`immediate` (imm and LM0 access in one row) |
| 2,300 / 1,433 / 942 / 556 | GRF0/GRF1 port conflicts in/out |
| 2,560 | uninitialized forwarding register (runtime error) |
| 1,801 / 1,447 / 596 / 534 | data race on T / GRF1 / GRF0 / LM1 |
| 1,024 | MAU `dmode` conflict |
| 236 | one-time mask entry conflict |
| ~4,500 | runtime "accessing MAU forwarding register failed" at various lines |

The dominant failure is structural: the baseline is already packed to one ALU
expression per row, so moving an expression onto another row almost always
collides in the issue fields (`mau/mau`, `lm0/immediate`, GRF ports).  When a
move is structurally legal, it either changes a forwarding/T/canvas distance
(data race, rejected by the assembler) or changes the produced output
(1,000+ mismatches).  The `repair_race` wave specifically tried to pay for the
data-race rejects with one nop and then delete a now-redundant nop; none of
the 1,369 new repaired programs was semantically correct.

Per-family submissions and outcomes (submissions, not distinct programs; some
families appear in several waves):

| family | submissions | accepted | accepted < 93 |
| --- | ---: | ---: | ---: |
| move (one expression) | 32,046 | 171 | 0 |
| move_row (whole row into one row) | 14,847 | 0 | 0 |
| dissolve (two expressions to two rows) | 6,195 | 0 | 0 |
| delete | 756 | 0 | 0 |
| merge (adjacent rows) | 361 | 0 | 0 |
| repair (copy elimination) | 154 | 0 | 0 |
| noforward (marker move) | 152 | 0 | 0 |
| relocate (row permutation) | 1,484 | 6 | 0 |
| swap (adjacent swap) | 587 | 74 | 0 |
| reorder (expression order) | 201 | 161 | 0 |
| split (row split) | 110 | 37 | 0 |
| insert_nop | 44 | 44 | 0 |
| commute (operand order) | 160 | 160 | 0 |
| const (equivalent literal) | 163 | 163 | 0 |
| addr (addressing form) | 147 | 147 | 0 |

The equivalence-preserving families (`commute`, `const`, `addr`, `reorder`,
`split`, `insert_nop`) behave exactly as expected: 100 % of `commute`,
`const` and `addr` rewrites verify, which is a useful positive control on the
scorer.  The packing families (`move`, `move_row`, `dissolve`, `merge`,
`delete`, `repair`) have 0 accepted word reductions.

## 5. Why 52 is unreachable from this transformation space

The baseline contains **66 ALU expressions, 41 MAU expressions, 8 nops, 3
L1BM/L2BM transfers, 2 MV, 1 mwrite, 1 mread**.  66 rows carry exactly one ALU
expression; 2 rows are MV.

Two hardware rules were confirmed directly against the official assembler
(`assemble3 --instruction-mode flat`):

* two ALU expressions in one row → `Instruction field conflict detected
  between 'alu' and 'alu'` (imm+ALU → `'alu'` vs `'immediate'`);
* an MV expression in a PE row → `Non PE operation after separator`.

Therefore **any program with the current instruction mix needs at least
66 + 2 = 68 words**.  Reaching 52 requires deleting or replacing at least 14
ALU expressions — an algorithmic redesign of the numeric/format-selection
pipeline (the T-chain, the 24 immediates, the canvas pack), not packing,
moving, merging or constant rewriting.  This campaign exhaustively covered the
one-step neighbourhood and 20,247 explicit one-word-reduction programs
(including chained partial dissolutions), and found none that are correct.

(L1BM/L2BM rows *can* share a line with an ALU/imm row — the assembler accepts
`l1bmd`/`l2bmd` + imm — so those three rows are packable in principle; every
move that tried it changed transfer timing and failed.)

## 6. Artifacts

* `best/` — baseline snapshot + `log.jsonl` (words, mismatches, chain).
* `cache/candidates.sqlite` — all 48,446 programs, results, zlib-compressed text.
* `logs/summary-*.json` — per-wave and per-family counters.
* `logs/agreement.json` — scorer-vs-official evidence.
* `logs/bench.json` — throughput table.
* `logs/final_report.json`, `logs/analyze-final.txt` — distributions, causes,
  row-count accounting.
* `harness/` — the harness (see `README.md`).

Reproduce the gate for the recorded best:

```sh
python3 tools/fbcheck.py  research/experiments/superopt/best/93w_9b36e271ad.vsm
python3 tools/fbverify.py research/experiments/superopt/best/93w_9b36e271ad.vsm
```
