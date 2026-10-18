# 09 — rescheduling / packing attempt: verdict and evidence

Date: 2026-10-18 (round 16)
Baseline: `problems/challenge/20.fizzbuzz/main.vsm` = **93 lines, ACCEPTED**
(`ACCEPTED!! score=93 j=91 m=2 bytes=3054`, re-confirmed with `problems/run_problem.py`
and `assemble3 --instruction-mode flat` at the start and end of this session).

**Verdict: no verified score < 93 was found, and the structure below shows why the
instruction sequence cannot be packed below 93 by rescheduling.** `main.vsm` was not
modified. No winning candidate was produced, so no new file was written under `attempts/`.

All candidates in this session were screened in this order:
`assemble3 --instruction-mode flat` (legality) → `fastsim.check` (native-sim + DRAM
`mism == 0`, semantics) → score. The assembler is the authority on hazards; fastsim is
the authority on value semantics (it also errors on a disabled forwarding register, so a
broken `$aluf`/`$mauf` pair is usually caught twice).

---

## 1. What the 93 lines are made of (unchanged, re-confirmed)

| line kind | count |
|---|---|
| ALU only | 37 |
| ALU + MAU | 27 (23 `mau+alu` + 4 `alu+mau`) |
| mwrite + ALU / mread + ALU | 1 / 1 |
| **MAU only** | **14** (13 `mau`, 1 `mau+noforward`) |
| nop | 8 |
| L1BM / L2BM / MV | 1 / 2 / 2 |

ALU 66, MAU 41. One ALU and one MAU per step, so line count ≥ ALU count = 66; with the
two MV statements (each a line of its own) the absolute floor is 68. A win needs exactly
one ALU to share a line with a MAU/nop/transfer that currently carries no ALU.

## 2. Forwarding-chain structure (the real rigid backbone)

`$aluf`/`$mauf` at step *s* reads the register written by the last ALU/MAU step *before s*
(same-step forwarding does not exist; `noforward` on a step suppresses the update and
leaves the previous value readable). `chains2.py` / `facts.py` compute the producer of
every forwarding read and group steps into **15 atomic components**:

```
[1,2] [3,4] [5,6] [7,8,9] [10,11,12,13] [14,15] [16,17] [21,22,23]
[26,27,28] [32,33,34,35,36,37] [38,39,40,41] [42,43,44,45,46,47,48]
[52,53,54,55] [78,79,80,81,82,83,84]
```

Every component is a run of consecutive steps whose members cannot be separated without
replacing a forwarding read by a real GRF read. Components span 2–7 steps; the 7-step
ones are the `lsub`/`fvadd` double chain (42–48) and the final pack (78–84). These steps
are already fully packed (an ALU and a MAU nearly everywhere), so they contribute no
free ALU slot.

**34 ALU instructions are not forwarding-locked** (`freealu.py`); they are the only freely
movable ALU work. Their categories and why they cannot move:

| free ALU(s) | constraint |
|---|---|
| L2 `imm 56`, L3 `imm 599`, L15 `imm 8`, L18/19/20 `imm 32/408/4672`, L22/23 `imm 13/66` | consumed by L7 / L25 (the `$r24v`/`$s28v` longword reads) - must stay before L25; the only free ALU slots before L25 are L17/L21, whose MAU writes GRF0 **and** GRF1 (`out_grf0`/`out_grf1` collisions). |
| L27/28 `imm 0x4b000030/0x4b00000a`, L29/30/31 reciprocal imms, L34 `imm 0.1`, L36 `imm 0x4b00007a`, L48/49 `imm 0.01/0.001`, L52/54/55/56 character imms | all consumed by the canvas writes (L60-L76) or the floating point chain; their deadlines are all `<= L61`. The only free slots before L61 are L17/L21 (bank collisions) and L40/L41/L50 (LM0: `imm`+LM0 is a hard field conflict). |
| L24 `isub ... $omr1`, L25 `iadd ... $n1/$imr1`, L33 `ipassa`, L39 `iadd/...`, L51 `fftoi`, L59/62/66/70/73 `ladd`, L77 `lpassa` | pinned by `omr1` (rewritten at L42), by T (the canvas position is per-PE data-dependent), or by the LM0 3-step port gap (§5b). |

## 3. Exhaustive local searches (all 0 winners)

| search | move class | candidates | assembled | winners |
|---|---|---|---|---|
| `search1.py` | relocate one instruction into a *new* line anywhere | 5449 | 3664 | 0 |
| `search2.py` | put one instruction **on** a nop step (nop replaced, source line deleted) | 920 | 613 | 0 |
| `search3.py` | **merge** one instruction into another step, delete its own line | 3726 | 1294 | 0 |
| `search5.py` | split a 2-instruction line: ALU → one line, MAU → another; source empties | 38773 | 5912 | 0 |
| `search6.py` | put **both** instructions of a 2-instruction line on one nop step | 240 | 112 | 0 |
| `search4.py` | relocate a whole forwarding component (see §5) | — | — | not run / blocked |

Every assembled candidate either raised a fastsim runtime error or produced mismatches;
none had `mism == 0`. Hence every way of *emptying a line* that does not change the
instruction sequence was enumerated: a single-instruction line empties only by merging
into another line (search3), a two-instruction line only by splitting into other lines
(search5) or onto one nop (search6).

## 4. Why the 14 MAU-only lines cannot take an ALU

The blocker is per-line **operand field conflicts**, not dependencies; `diag_merge.py`
prints the assembler's verdict for all 66 ALUs on each of these lines.

| MAU-only line | MAU accesses | why no ALU fits |
|---|---|---|
| L17 `fvadd $aluf -$t $lr102v $ls102v $ln102v` | reads GRF0+GRF1; **writes GRF0+GRF1+LM1** | any ALU writing GRF0/GRF1 collides with `out_grf0`/`out_grf1`; any ALU reading GRF0/GRF1 at other addresses collides with `in_grf*`; `imm` is out for the same reason. Only a GRF-free ALU (T/LM0/`nowrite` only) fits, and the only such ALUs (L1 `ipackbit`, L32 `ior $t $n1`) are forwarding heads with no GRF destination, so they cannot be decoupled. |
| L21 `fvadd $lr102v $ls108 $lr110v $ls110v $ln110v` | same | same |
| L40/L41 `fvfma … $m17v2 / $m25v2` | **writes LM0**; reads GRF0+GRF1 | `imm`+LM0 is a hard field conflict; an ALU touching LM0 conflicts with `out_lm0`; an ALU reading GRF0/GRF1 conflicts with `in_grf*`. |
| L50 `fvfma $s20 $r130 $mt[43,41,0,0] $s48v/1100` | LM0 (T-indirect read), GRF0+GRF1 read, GRF1 write | `imm`+LM0 forbidden; `out_grf1` taken; GRF0/GRF1 reads collide. |
| L60/61/64/65/68/69/72/75/76 `fvpassa/$imr15 … $mt…` or `$lm0v` | LM0 write (T-indirect or absolute); reads GRF0 | `imm`+LM0 forbidden; an ALU reading GRF0 at another address collides with `in_grf0`; an ALU writing GRF0 *is* allowed, but no semantically available ALU at steps 60–76 writes GRF0: the only remaining work there is the pack (reads LM0, collides) and the imm at L78 (imm+LM0). |

None of the 34 non-forwarding-locked ALUs can move to those positions either: imms cannot share an LM0
line at all, and the non-imm free ALUs are pinned by T (the canvas position is
data-dependent), by `omr1` (rewritten at L42), or by an earlier consumer (see §2 table).

## 5. Why the 8 nops cannot be filled

All 8 nops are load-bearing; deleting any one gives an assembler `DataRaceError`:

- **63/67/71/74**: T-write → T-read gaps. The preceding `ladd` writes T and the next
  T-indirect canvas write must start ≥ 2 steps later (`cycles(7)` on T).
- **85**: separates the pack's last `$s0v/1100` write (L84) from `l1bmd`'s `$ls0` read
  (L86).
- **87/88**: `l1bmd` → `l2bmd` needs `Steps(3)`.
- **91**: `l2bmd` → `mvd` needs `Steps(2)`.

Replacing a nop by an ALU *keeps the step*, so it would be a valid win if an ALU were
available there — but the only ALUs whose consumers come after step 63 are L57/L58 (LM0
T-indirect: their T is not yet the value of that region), L77 (writes T too early), and
the pack (LM0 conflict, and it must follow L77). Hence `search2.py` finds nothing.

The tail is exactly minimal:
`pack end 84 → +2 l1bmd 86 → +3 l2bmd 89,90 → +2 mvd 92 → +1 mvp 93`.
Shifting any of it later adds a line; shifting earlier violates the same rules.

## 5b. The one concrete "near miss": renaming the `r18/r19` longword and merging `lpassa`

The last canvas-write step is L76 (`fvpassa/$imr15 $r67v $mt42v`) and L77 is
`lpassa $lr18 $t` (the T finalisation). It is tempting to merge L77 into L76:

- `lpassa $lr18` reads GRF0 at 18-25; L76's MAU reads GRF0 at 67-70 -> `in_grf0`.
- Fix by renaming the value: `fftoi $mauf $r19` -> `$s201`, `lsub $lr18 $ls132 $omr1`
  -> `lsub $ls200 $r24 $omr1` (s200 is an untouched zero word, r24 is the untouched
  zero high word of the constant longword; the flags are unchanged because
  `x - 0 == x`), and `lpassa $ls200 $t`.
  This assembles: the field conflicts are gone and the T read (MAU, T-indirect) and
  T write (ALU) in one step are accepted.

It is then rejected by the **LM0 port rule**, not by the merge:
`PortConflictError: A LM0 memory port is unavailable at line 78` after L77 is deleted.
The rule is address-independent (`Steps(3)` for any LM0/LM1 write followed by an LM0/LM1
read). The last canvas write is L76 and the pack's first LM0 read is L79, so L77 **and**
L78 are both required as steps. Merging `lpassa` therefore only makes L77 an empty step,
and no ALU is available to fill it, so the count stays 93. (Recorded for future rounds:
the rename itself is verified-good and is the right way to free GRF0 in that line.)

## 6. Why a general scheduler (the VProgram route) cannot do better either

`mncompile.schedule` would reallocate register values and could break forwarding chains
by materialising values into GRF. The packing blockers above are **not** register
allocation problems, though:

- `imm` + LM0 in one line is a fixed instruction-encoding conflict (shared operand
  bits); renaming or re-materialising cannot remove it. So the 10 canvas MAU-only lines
  can never take one of the 24 `imm` ALUs.
- L17/L21 program their MAU to write GRF0, GRF1 **and** LM1. Whatever storage the
  scheduler chooses, an ALU that writes any of those banks on the same line still hits
  `out_grf*`/`out_lm1`; only GRF-free ALUs are possible, and the register-free ALUs are
  the two forwarding heads that cannot be decoupled (their result has no destination
  other than the forwarding bus).
- L40/L41/L50 write LM0, so again `imm` is excluded and LM0-touching ALUs collide.

A relabelled SSA schedule would also have to keep the canvas writes in their exact
T-relative order (T is per-PE data-dependent) and keep the constant block `r24..r31`
packed as longwords (`$r24v`, `$s28v` reads span two differently-written words), so the
freedom a scheduler would gain is much smaller than the ALU count suggests.

## 7. Scripts left in this directory

- `search1.py`, `search2.py`, `search3.py`, `search5.py`, `search6.py` — exhaustive move
  searches (nop/merge/pair-split/pair-to-nop).
- `diag_merge.py`, `diag_ok.py` — per-target assembler verdicts for the MAU-only lines.
- `chains.py`, `chains2.py`, `facts.py`, `freealu.py` — forwarding producers, components,
  non-forwarding-locked ALUs, MAU-only lines, nop positions.
- `ideal.py`, `ideal2.py` — idealized schedulers ignoring operand-field conflicts; they
  are not sound (a raw-Fwd read must be *exactly* the previous step) and were not used
  as evidence.

## 8. Recommendation

93 is a local **and** structural optimum for this instruction sequence. Reaching 53 (or
even 92) requires removing instructions — fewer ALU operations (constant generation,
digit stage, pack), which is the algorithm route already explored in `06`/`08`, not
rescheduling. If a scheduler is still desired, the only remaining in-sequence lever is
*dead destination removal* (e.g. proving LM1 words 104/106/108 of L17's `$ln102v` are
never read) so that an MAU writes one bank instead of three; that changes instructions,
not their placement.
