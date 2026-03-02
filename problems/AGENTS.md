# AGENTS.md

## run_problem.py の使い方

`run_problem.py` は、`problems/<問題名>/` 配下の `testcase*.vsm` をまとめて実行し、公式 `judge.py` で解答を検証するためのスクリプトです。

### 前提

- `judge/judge-py/judge.py` が存在すること（未配置なら `setup_judge.sh` を先に実行）
- 問題ディレクトリに `testcase.vsm` または `testcase*.vsm` があること
- 解答ファイル（`.vsm`）を用意していること

### 基本実行

リポジトリルートで実行:

```bash
python3 problems/run_problem.py <problem> --solution problems/<problem>/<solution>.vsm
```

`problems/` ディレクトリ内で実行:

```bash
python3 run_problem.py <problem> --solution <problem>/<solution>.vsm
```

例:

```bash
python3 problems/run_problem.py 1.a-b --solution problems/1.a-b/3lines.vsm
```

### 主なオプション

- `problem`:
  - 問題名またはパス。相対パスは `problems/` 起点で解決される。
- `-s, --solution <path>`:
  - 解答 `.vsm` のパス。省略時は `problems/<problem>/solution.vsm`。
- `-j, --judge <path>`:
  - `judge.py` のパスを明示する。
- `-v, --verbose`:
  - `inputs / expect / actual` セクションも表示する。
- `--keep-going`:
  - 失敗ケースが出ても残りの testcase を継続実行する。
- `--raw-judge-output`:
  - フィルタせず judge の標準エラー出力をそのまま表示する。

### よく使う実行例

詳細付きで確認:

```bash
python3 problems/run_problem.py 1.a-b --solution problems/1.a-b/3lines.vsm -v
```

失敗しても全 testcase を回す:

```bash
python3 problems/run_problem.py 1.a-b --solution problems/1.a-b/3lines.vsm --keep-going
```

judge の生出力でデバッグ:

```bash
python3 problems/run_problem.py 1.a-b --solution problems/1.a-b/3lines.vsm --raw-judge-output
```

## 7.sumcol-mini で躓いた点（Top: 4 lines）

- `fvadd $m0v $m4v $nowrite` は `Instruction field conflict detected between 'lm0' and 'in_lm0'` で失敗する。  
  - 同一命令で LM0 を 2 本直接読む形が衝突するため、`fvpassa ... $nowrite` で `mauf` に流し、次行以降で `fvadd $... $mauf ...` として連鎖させる。

- Flat 指定と `v` 指定を同時に書くとパースエラーになる。  
  - 例: `fvpassa $m[0,2]v $nowrite` は `Cannot use flat notation ... with ADRI notation`。

- `m`（単語）で Flat 指定すると、今回の `sumcol-mini` では奇数インデックス側が 0 になりやすい。  
  - 例: `$m[0,2,0,2]` 系は `[x0,0,x2,0,...]` のような結果になった。
  - `lm`（長語）に切り替えると正しく 2 Float 単位で処理できる。

- `llm`（2長語）を `fvadd/fvpassa` に使うと値不一致になりやすく、今回の問題では不適だった。

- 最終的に通った 4 行パターン（score=4）:

```vsm
fvpassa $lm[0,2,0,2] $nowrite
fvadd $lm[4,6,4,6] $mauf $nowrite
fvadd $lm[8,10,8,10] $mauf $nowrite
fvadd $lm[12,14,12,14] $mauf $ln[0,2,0,2]
```

## 8.sumcol で躓いた点（Top: 11 lines）

- `8.sumcol` には `problem.md` が無く、仕様は `testcase.vsm` の末尾（`Out(0)` の `d getd`）から読み取る必要があった。  
  - 実質的には「`256x16` の列和を取り、16要素を `DRAM d0..d7` に出力する」問題。

- `fvadd ... $lr0v` で `GRF0` に書いた直後に `l1bmm@0 $lr0v $lb0` を置くと、`DataRaceError (GRF0 address 0)` で落ちる。  
  - `GRF0` 同一アドレスの read-after-write には 1 ステップ空ける必要があり、`nop` 1 行を挟むと解消。

- `l1bmm@0` の直後に `l2bmrffadd` を近接配置すると、`DataRaceError (L1BM address 0)` で落ちる。  
  - `PE→L1BM` の後に同一アドレスを `L1BM→L2BM` で読むにはステップ間隔が必要で、今回は `nop` を 3 行挿入して通った。

- 縮約経路は以下で安定した。  
  - `l1bmm@0 $lr0v $lb0`（MAB方向を畳む）
  - `l2bmrffadd $lb0 $lc0`（L1B方向を畳む）
  - `mvrffadd/n64 $lc0 $d0`（group/L2B方向を畳み、DRAMへ出力）

## 10.sumrow で躓いた点（Top: 160 lines）

- `sum_row_mini`（16行）をそのまま出すと、`16 value(s) correct, but 240 value(s) mismatch` になる。  
  - 理由は入力配置が `4_L2B` に分散され、`(64:2)` の並びを全域で処理しないといけないため。mini の1ブロック分しか計算できていなかった。

- 各 PE では「`m{base}..m{base+3}` を `v4` で足して1出力」を 16 回繰り返す必要がある。  
  - `base = 0, 16, 32, ..., 240`、出力先は `n0, n4, ..., n60`。

- `256x16` の内側 16 要素和は、`mauf` と `r0v`/`s0v` を使った 10 命令パターンで安定した。  
  - `fvpassa -> fvadd x3 -> msr/fvadd/msr/fvadd/msr/fvadd` の流れを1ブロックとして展開。

- 行数が多く手書きミスしやすいので、同型ブロックの自動生成前提で作る方が安全だった。  
  - 最終的に 160 行・`bytes=3452` で `run_problem.py` で Accept を確認。

## 9.sumrow-mini で躓いた点（Top: 8 lines）

- `fvadd $r0v4 $r1v4 $r0v4` は `Instruction field conflict detected between 'in_grf0' and 'in_grf0'` で失敗する。  
  - 同一命令で `GRF0` を 2 入力同時参照できないため、`aluf` フォワーディングを使う形に寄せる必要があった。

- `GRF0`/`GRF1` を使った「加算値保持 + シフト値保持」は、8行に詰めると `DataRaceError`（`GRF0 address 0` / `GRF1 address 0`）が出やすい。  
  - `nop` を入れれば回避できるが、行数が増えて Top:8 を満たせなくなる。

- `mauf` をそのまま使い回すと、ALU命令を挟んだ後に `Accessing to MAU forwarding register failed ... MAU is disabled` で落ちるケースがあった。  
  - `fvpassa $mauf $nowrite` を都度入れて `mauf` を更新し直すと安定した。

- 8行達成には `;` での同時発行が有効だった。  
  - `fvadd ... ; msl ...` を同一ステップで発行して、PE間シフト3回を追加行なしで重ねられた。

- 最終的に通った 8 行パターン（score=8）:

```vsm
fvpassa $m0v4 $nowrite
fvadd $m1v4 $mauf $nowrite
fvadd $m2v4 $mauf $nowrite
fvadd $m3v4 $mauf $nowrite
fvpassa $mauf $nowrite;msl $mauf $nowrite
fvadd $mauf $aluf $nowrite;msl $aluf $nowrite
fvadd $mauf $aluf $nowrite;msl $aluf $nowrite
fvadd $mauf $aluf $n0v
```
