| stage | words | ALU expr | MAU expr | imm expr | imm-only words | nop words |
|---|---|---|---|---|---|---|
| S0 prologue constant dance (GRF0 1..7 via dmwrite/dmread/iinc) | 4 | 4 | 2 | 2 | 0 | 0 |
| S1 block-coordinate build (bit gather l1bid/peid/l2bid) | 9 | 9 | 0 | 0 | 0 | 0 |
| S2 base/threshold/mask setup (2^23 float trick, n1=8b+8, compare masks) | 12 | 10 | 6 | 7 | 4 | 0 |
| S3 digit estimate + Fizz/Buzz selection (reciprocals, lsub T-chain) | 24 | 22 | 17 | 10 | 4 | 0 |
| S4 canvas value/position (scroll offset, fftoi to T) | 7 | 6 | 4 | 4 | 1 | 0 |
| S5 canvas drawing (T-register character writes + 4 nop) | 21 | 8 | 14 | 0 | 0 | 4 |
| S6 pack 8 bytes into one long word | 7 | 7 | 0 | 1 | 1 | 0 |
| S7 transfer (l1bmd, 2x l2bmd, mvd, mvp) + 4 nop | 9 | 0 | 0 | 0 | 0 | 4 |
| **total** | **93** | **66** | **43** | **24** | **10** | **8** |

line classes:
  ALU only              37
  ALU + MAU co-issued   29
  MAU only (ALU slot free) 14
  nop                   8
  block/L1BM/L2BM only  3
  MV                    2
  check sum             93
