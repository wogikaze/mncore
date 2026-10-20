# Every DRAM-writing MV form and its maximum output per instruction word

Scope: MN-Core 2 SDM chapter 3.5.8, all basic modes whose destination is DRAM.
The transfer count `n` is in **long words** (8 bytes).  The assembler field limit
is measured with the official `assemble3`: `n=16384` is accepted, `n=32768` is
rejected with a bitfield overflow (`logs/probe_isa.txt`).  Therefore the largest
transfer any MV word can specify is 16384 long words = 131072 bytes.

| SDM | form (assembler opcode) | words written to one group's DRAM | max bytes to Group 0 | max bytes all groups |
|---|---|---|---|---|
| 3.5.8.2 | PDM→DRAM single individual (`mvp/n $p@0 $d@0`) | n | 131072 | 131072 |
| 3.5.8.7 | L2BM→DRAM single individual (`mvp/n $lc@0.1 $d@0`) | n | 131072 | 131072 |
| 3.5.8.12 | L2BM→DRAM parallel (`mvp/n $lc@.1 $d`) | n | 131072 | 524288 |
| 3.5.8.14 | L2BM→DRAM group-intra reduction (`mvr2<op>/n $lc $d`) | n | 131072 | 524288 |
| 3.5.8.17 | L2BM→DRAM inter-group combined reduction (`mvr4<op>/n $lc $d`) | n/2 | 65536 | 262144 |
| 3.5.8.21 | L2BM→DRAM inter-group reduction (`mvr<op>/n $lc $d`) | n/4 | 32768 | 131072 |
| 3.5.8.24 | PDM→DRAM distribution (`mvd/n $p@0 $d0`; see note) | n/4 | 32768 | 131072 |

Note on 3.5.8.24: this assembler accepts `mvd/n $p0@0 $d0` (no group
suffix on the destination; `$d0@0` is rejected with "Group ids or l2bm ids
... invalid") and `mvd/n16384 $p0@0 $d0` assembles.  The separate PDM→DRAM
single-individual copy `mvp/n $p0@0 $d0@0` is also accepted and writes n words
to one group (`logs/mvp16384.txt` writes words 0, 8191 and 16383 with one
`mvp/n16384`).  Both are bounded by 16384 long words/word; the table row is the
distribution form's n/4 words to Group 0.

Forms 3.5.8.3/4/5/6/8/9/10/11/13/16/18/19/20/22/23/25 do not write DRAM
(they write PDM or L2BM, or read DRAM), so they cannot contribute to the
32766-byte output.

## Consequence (target 1 of the brief)

`words >= ceil(32766 / 131072) = 1`.

The DRAM write hop is therefore **not** the bottleneck: one instruction word can
write 16 times the whole output.  The binding hop is L1BM→L2BM, whose largest
instruction (`l2bmd`) moves 2048 long words = 16384 bytes per word; see
`README.md` §3 and the 8-word delivery bound.
