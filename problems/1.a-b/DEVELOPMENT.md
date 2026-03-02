# 1.a-b Tooling

## Known passing 3 lines

```vsm
fpassa $llm16v $llr0v
fvadd $lm[0,4,8,12] -$aluf $ln[0,4,8,12]
fvadd $lm[2,6,10,14] -$lr[2,6,10,14] $ln[2,6,10,14]
```

## Quick check

```bash
python problems/run_problem.py 1.a-b --solution problems/1.a-b/3lines.vsm
```

## Raw judge output (for parse/hazard debugging)

```bash
python problems/run_problem.py 1.a-b --solution problems/1.a-b/3lines.vsm --raw-judge-output
```

## Baseline (known passing in this repo)

```bash
python problems/run_problem.py 1.a-b --solution problems/1.a-b/4lines.vsm
```

## Direct assemble3 + emulator

```bash
python docs/scripts/run_assemble3_emu.py \
  --testcase problems/1.a-b/testcase.vsm \
  --solution problems/1.a-b/3lines.vsm
```

`gpfn3_package_main` is useful for debug dumps, but it does not compare output against expected values.
Use `run_problem.py` for pass/fail.

## Notes

- `fpassa` uses `aluf` forwarding (not `mauf`).
- `fpassa ...` -> immediate GRF read often causes `DataRaceError`; split work across `aluf` and delayed GRF read.
