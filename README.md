# MN-Core Simple Graph Compiler for Education

『MN-Coreグラフコンパイラを自作して MNIST を学習させよう！』の学習用グラフコンパイラのリポジトリです。

MN-Core2 用のアセンブリを出力し、MN-Core2 エミュレータを使って多層パーセプトロン（MLP）を用いた MNIST 分類器を動作させるところまで体験できます。

詳しくは以下のブログ記事、スライド、MN-Core Challenge の特設問題セットをご覧ください。
- [ブログ](https://tech.preferred.jp/ja/blog/mn-core2_graphcompiler_scratch/)
- [スライド](https://speakerdeck.com/pfn/202512_mncore-graph-compiler-mnist)
- [MN-Core Challenge の特設問題セット](https://mncore-challenge.preferred.jp/mnist/)


## 対応環境
- Ubuntu 22.04 (WSL 可)
- mac（Docker 必須）

## 必要環境
- Python 3.10+

## セットアップ
```bash
pip install -r requirements.txt
bash setup_judge.sh
```

## Challenge Problem Toolchain

### Error-budgeted high-level compiler (prototype)

[mncompile](mncompile/README.md) compiles restricted Python kernels through LLVM
to MN-Core VSM, selecting the shortest generated candidate within a specified
input domain and absolute error budget. It records error bounds, candidate costs,
and optimized LLVM IR. All 25 original Challenge problems have readable high-level
sources and generated VSM accepted by the official judge. The 22 eligible shortest
references are matched; three references with reproduced domain-valid
counterexamples are excluded from the line target, prioritizing correctness.
See the [comparison report](mncompile/benchmarks/challenge/generated/progress.json)
and [reference audits](mncompile/benchmarks/challenge/reference-audits.json).

For `x + 0.001*x*x` on `[-1, 1]`, changing the budget from
`1e-5` to `0.002` reduces the generated program from 13 lines to 1 per 8 Floats/PE.

```bash
python3 -m mncompile mncompile/examples/near_identity.py --domain -1 1 --atol 0.002 --output /tmp/mncompile-demo
```

LLVM `opt` is required. See the linked README for the supported language subset,
the numerical model underlying the bounds, and official assembler/emulator checks.

### Running challenge testcases

1. Place the official MN-Core Challenge testcase under `problems/<problem-name>/` (e.g. `problems/1.a-b/testcase.vsm`).
2. Run `bash setup_judge.sh` once so that `judge/judge-py/judge.py` and the docker image for the assembler/emulator are available.
3. Write your candidate solution VSM (for example `problems/1.a-b/solution.vsm`).
4. Execute the helper to run every testcase in that directory:

	```bash
	python problems/run_problem.py 1.a-b --solution problems/1.a-b/solution.vsm -v
	```

	The script forwards each `testcase*.vsm` to the official judge and surfaces the exit status so you can iterate quickly.
	Use `--raw-judge-output` to inspect unfiltered parser/hazard errors from `judge.py`.

### Bootstrap `problems/` from MNIST challenge pages

Use the sync helper to auto-create numbered `problems/<index>.<name>/` directories and fetch each `testcase.vsm`:

```bash
python problems/sync_mnist_problems.py
```

If the testcase endpoint requires login, pass your cookie header:

```bash
python problems/sync_mnist_problems.py --cookie 'sessionid=...'
```

When online fetch fails, the script falls back to `testcases/<slug>.vsm` if present.

### Original MN-Core Challenge problems and answers

The original [25 Challenge problems](https://mncore-challenge.preferred.jp/problems/)
are stored separately in [problems/challenge](problems/challenge/README.md).
Each includes `problem.md`, official `testcase*.vsm`, an Accepted public submission
in `answer.vsm`, and an editable copy in `main.vsm`. `answer.md` / `answer.json`
record the submission URL, author, and line count. Tutorial answers are also saved
as `official.vsm` when published.

Fetch missing files (existing files are preserved):

```bash
uv run --with beautifulsoup4 python problems/sync_challenge_problems.py
```

The helper selects the shortest submission per problem linked from the standings,
checks its problem and Accepted status, and preserves the original code.
Run an answer against its official testcases with:

```bash
python3 problems/run_problem.py challenge/12.convert-endian --solution problems/challenge/12.convert-endian/answer.vsm
```

The original Challenge's [judge.zip](https://mncore-challenge.preferred.jp/judge.zip)
can also be used via `--judge /path/to/judge/judge-py/judge.py`.
The runner adapts older testcase output separators in a temporary copy.

`npm run sync-problems` in `viz/web` includes both problem sets in the visualizer.

### Low-level tools

- `fx_export/tools/assembler`: wraps the dockerized MN-Core assembler (`assemble3`) so you can assemble standalone VSM without running the full judge.
- `fx_export/tools/emulator`: runs the emulator (`gpfn3_package_main`) against an assembled binary for ad-hoc experiments.

Both scripts build the `mncore-challenge` docker image automatically on first use.

### Strategy Notes

- Blog-derived challenge strategy notes: `docs/challenge_strategy_from_primenumber_2024-09-26.md`
