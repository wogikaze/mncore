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

### Low-level tools

- `fx_export/tools/assembler`: wraps the dockerized MN-Core assembler (`assemble3`) so you can assemble standalone VSM without running the full judge.
- `fx_export/tools/emulator`: runs the emulator (`gpfn3_package_main`) against an assembled binary for ad-hoc experiments.

Both scripts build the `mncore-challenge` docker image automatically on first use.

### Strategy Notes

- Blog-derived challenge strategy notes: `docs/challenge_strategy_from_primenumber_2024-09-26.md`
