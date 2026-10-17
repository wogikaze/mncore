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

### mncompile: generic compiler for Python kernels

[mncompile](mncompile/README.md) compiles an ordinary Python `kernel(...)` plus a tensor contract
(dtype, value range, physical layout in the official notation, absolute error budget) to MN-Core 2 VSM.
It contains no problem-specific kernels or handwritten assembly: strategies (local maps, relayout,
reductions within a PE/MAB, matrix-unit contractions, hierarchical reductions through L1BM/L2BM/MV,
output splitting over replicated MABs, all-pairs reductions, data movement, constant generation)
produce candidate programs, a VLIW scheduler places them, every candidate is verified by simulation,
and the shortest one is kept. Approximations (Newton steps, polynomial degree, dropping terms that fit
the error budget) are searched under the budget.

On the 73 problems (25 original Challenge + 48 MNIST set) every generated program is accepted by the
official judge; 16 are at or below the reference line counts, including 3 strictly below.
The benchmark compares general compilation with an optional mode specialized to the official inputs.
See the table in
[mncompile/README.md](mncompile/README.md) and the generated programs in `mncompile/benchmarks/results/`.

```bash
python3 -m mncompile mncompile/examples/sigmoid_like.py --contract mncompile/examples/sigmoid_like.json --output /tmp/out
python3 -m mncompile.bench.run --output /tmp/bench        # all 73 problems with the official judge
```

### Lean optimality audit

[proofs_lean](proofs_lean/README.md) records the formal-proof audit separately from benchmark scores.
The previous `optimalProven` labels were unsupported and have been withdrawn. Full-ISA optimality
is currently unproven for all 73 problems. The replacement framework checks semantic certificates,
enumeration completeness, and the distinction between general and testcase-only correctness.

```bash
python3 proofs_lean/scripts/check.py
python3 -m unittest discover -s proofs_lean/tests -v
```

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

The original Challenge's [judge archive](https://mncore-challenge.preferred.jp/judge-mncore-challenge.zip)
can also be used via `--judge /path/to/judge/judge-py/judge.py`.
The runner adapts older testcase output separators in a temporary copy.

`npm run sync-problems` in `viz/web` includes both problem sets in the visualizer.

### Low-level tools

- `fx_export/tools/assembler`: wraps the dockerized MN-Core assembler (`assemble3`) so you can assemble standalone VSM without running the full judge.
- `fx_export/tools/emulator`: runs the emulator (`gpfn3_package_main`) against an assembled binary for ad-hoc experiments.

Both scripts build the `mncore-challenge` docker image automatically on first use.

### Strategy Notes

- Blog-derived challenge strategy notes: `docs/challenge_strategy_from_primenumber_2024-09-26.md`
