# superopt — automated superoptimization harness for FizzBuzz (93 → ≤52)

This directory is a self-contained search harness for the MN-Core 2 FizzBuzz
answer (`problems/challenge/20.fizzbuzz/answer.vsm`, 93 assembled words,
j=91 m=2).  The harness scores candidates with the native simulator through
`tools/fbcheck.py`, filters them with the official assembler, caches every
result by program hash, and records any improvement under `best/`.

Nothing in `tools/`, `problems/` or `docs/` is modified.

## Layout

```
harness/vsmx.py             row-level program model (parse / canonical emit,
                            unit classification, issue pre-filter)
harness/transforms.py       transformation library (14 families)
harness/scorer.py           two-stage scorer + SQLite cache + worker pool
harness/campaign.py         wave-based campaign driver (seed/singles/moves/
                            dissolve/probe/anneal/plateau)
harness/bench.py            throughput benchmark (serial and parallel)
harness/verify_agreement.py scorer-vs-official-tools evidence
harness/report.py           query the cache and print the result tables
cache/candidates.sqlite     every evaluated candidate (hash → result + text)
best/                       every improved candidate + log.jsonl
logs/                       campaign logs, summaries, agreement evidence
```

## Scorer

Two stages, both cached by `sha256(program text)`:

1. **official assembler pre-filter** (`mncompile.sim.assembler`, the same
   `assemble3` that `tools/fbverify.py` runs, ~6 ms).  It rejects field
   conflicts, data races and unsupported forms.  This filter is sound: an
   assembler error is a hard reject for the official gate too.
2. **native simulator** (`tools/fbcheck.check`, ~0.45 s): runs the program
   against the official testcase and compares all 4096 `d getd` long words.
   The word count is the assembled `j`+`m` count; it is cross-checked against
   the assembler count.

Workers are spawned processes with `RAYON_NUM_THREADS=1`; each worker owns one
native simulator process.  The cache is SQLite (WAL) and stores the
zlib-compressed program text, so best candidates can be recovered without
rerunning anything.

Measured throughput (`harness/bench.py`, 60 candidates, 2026-10-20, shared
12-core host under load ~4):

| workers | candidates/s | simulator runs/s |
| ---: | ---: | ---: |
| 0 (serial) | 2.2 | 2.2 |
| 4 | 4.9 | 4.9 |
| 8 | 6.9–8.1 | 6.9–8.1 |
| 10 | 7.4–9.0 | 7.4–9.0 |
| 12 | 7.0–7.4 | 7.0–7.4 |

The campaign workload mixes assembler rejects (~6 ms) with simulator runs
(~0.45 s); its effective rate is 7–14 candidates/s depending on the fraction
of candidates the assembler rejects.

## Transformation library

| family | action | word effect |
| --- | --- | --- |
| `delete` | drop a row (nop or instruction) | −1 |
| `repair` | drop a pass-through copy and substitute its source at later uses | −1 |
| `merge` | fuse two adjacent rows (both operand orders) | −1 |
| `split` | split a row into two (intermediate for moves) | +1 |
| `move` | move one expression to any compatible row (append/prepend) | 0 or −1 |
| `move_row` | move all expressions of a row into one other row (nop fill) | −1 |
| `dissolve` | move both expressions of a 2-expression row to two other rows | −1 |
| `relocate` | move a whole row to another position | 0 |
| `swap` | exchange two adjacent rows | 0 |
| `reorder` | swap the expressions inside a row | 0 |
| `commute` | swap two memory-form sources of a commutative op | 0 |
| `const` | replace an immediate with an equivalent literal | 0 |
| `addr` | rewrite an addressing form (compact ↔ flat, T spelling) | 0 |
| `noforward` | move the `noforward` marker to another row | 0 |
| `insert_nop` | insert a nop (repair for a later move) | +1 |

The issue pre-filter (`vsmx.can_host`) only encodes rules we are sure of: one
ALU expression per line, MV alone, at most two MAU groups, one
mwrite/mread/noforward per line.  The simulator's `issue::check` and the
official assembler remain the real gates.

## Campaign waves

* `seed` — baseline, official-gate cross-check.
* `singles` — every one-step mutation of the 11 word-reducing/neutral
  families (~11k candidates: 93 deletes, 184 merges, 8.5k relocations,
  ~2k row moves into free slots, commutations, constants, address rewrites).
* `moves` — every single-expression move to every compatible row (~13k
  candidates), including moving all expressions of a row into a nop slot.
* `dissolve` — both expressions of each 2-expression row to two other rows,
  nearest hosts first (~4k candidates).
* `probe` — a random sample of moves evaluated *without* the assembler
  filter, to record the simulator mismatch distribution of candidates the
  assembler rejects.
* `plateau` — beam over word-neutral, simulator-OK states recovered from the
  cache: samples further mutations from a pool of correct states, so a
  two-step dissolution (move one expression, then the other) is reachable.
* `anneal` — simulated annealing with the same move set.

Every wave streams through the scorer; the cache makes reruns free.

## Reproduce

```sh
cd research/experiments/superopt
python3 harness/verify_agreement.py          # scorer ↔ official tools
python3 harness/bench.py                     # throughput
python3 harness/campaign.py --tag main \
    --waves seed,singles,moves,dissolve --workers 10
python3 harness/campaign.py --tag plateau \
    --waves seed,plateau --workers 10 --plateau-evals 6000
python3 harness/report.py                    # result tables
```

`tools/fbverify.py best/<candidate>.vsm` is the final gate for any claim.

## Results

See `RESULTS.md` (campaign numbers, best candidate, failure modes) and
`logs/agreement.json`.
