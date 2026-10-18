# 00-worktree — fizzbuzz-shorten

## Worktree

- Location: `/home/wogikaze/wgkz/mncore/.worktrees/fizzbuzz-shorten`
- Branch: `recursive/fizzbuzz-shorten` (base: `origin/master` = `5712713`, remote と一致確認済み)
- Git-ignore: `.worktrees/` と `.recursive/` を `.git/info/exclude` に追加（共有 exclude、追跡ファイルは変更なし）
- Check: `git check-ignore -v .worktrees/x` → `.git/info/exclude:7:.worktrees/`
- Codex側 (`/tmp/mncore-welcome-lb`, `codex/welcome-one-line-lower-bound`) はそのまま継続。本方針は origin/master から切っておりファイル範囲も分離（RRN.lean 等には触れない）。

## Setup

- `cp -a judge .worktrees/fizzbuzz-shorten/judge`（judge は git ignored。worktree に無いため main からコピー）
- 追加インストール不要（system python3 で judge 実行可）

## Baseline

- 対象: `problems/challenge/20.fizzbuzz/main.vsm`（ユーザー貼付の93行候補を配置）
- コマンド:
  ```bash
  python3 problems/run_problem.py challenge/20.fizzbuzz --solution problems/challenge/20.fizzbuzz/main.vsm
  ```
- 結果: `ACCEPTED!! score=93 j=91 m=2 bytes=3054`
- 参考: `answer.vsm` (tails, 公開 Accepted) は score 98。`lpha100.vsm` は別実装の120行。

## Normalized diff basis

- Baseline type: accepted local candidate
- Baseline reference: `main.vsm` @ 93行候補（score 93）
- Comparison reference: 以後の短縮候補（同一 testcase）
- Normalized baseline: `j + m` (flat instruction count) = 93
- Normalized comparison: `j + m` (flat instruction count)
- Normalized diff command:
  ```bash
  python3 problems/run_problem.py challenge/20.fizzbuzz --solution <candidate.vsm>
  ```

## Run context

- 以降の作業はすべて `.worktrees/fizzbuzz-shorten` から実行する。
- 目的: score (j+m) を 93 未満へ短縮し、Accepted を維持する。
- 参考文書: `docs/shortening_techniques.md`

## TODO

- [x] worktree 作成と ignore 確認
- [x] judge 配置とベースライン Accepted 確認
- [ ] score < 93 への短縮（候補ごとに judge で検証）
