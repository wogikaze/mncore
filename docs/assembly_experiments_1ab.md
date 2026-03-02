# 1.a-b Assembly Experiments (assemble3 + gpfn3_package_main)

## Result

`problems/1.a-b/3lines.vsm` は `ACCEPTED (score=3)`。

```vsm
fpassa $llm16v $llr0v
fvadd $lm[0,4,8,12] -$aluf $ln[0,4,8,12]
fvadd $lm[2,6,10,14] -$lr[2,6,10,14] $ln[2,6,10,14]
```

## Repro

```bash
python problems/run_problem.py 1.a-b --solution problems/1.a-b/3lines.vsm
python problems/run_problem.py 1.a-b --solution problems/1.a-b/3lines.vsm --raw-judge-output
```

## Key Findings

1. `fpassa` のフォワーディングは `mauf` ではなく `aluf`。  
   `fpassa ...` の次ステップで `mauf` を読むと
   `MAU forwarding register failed / MAU is disabled` で落ちる。

2. `fpassa $llm16v $llr0v` は GRF に B(16..31) を保持できる。  
   ただし次ステップで同アドレスを読むと `DataRaceError` になりやすい。

3. 2行目は `aluf` を使い、3行目は GRF を読む構成に分離すると安定する。  
   2行目で `ln[0,4,8,12]`、3行目で `ln[2,6,10,14]` を埋めることで 16 列を完成できる。

4. Flat アドレス指定 (`$lm[0,4,8,12]` など) で
   「どの列をどのステップで埋めるか」を明示すると 3 行化しやすい。
