# 解の一覧

| ファイル | 語数 (j+m) | 状態 | 検証 |
|---|---|---|---|
| `02_fable_47.vsm` | 47 (j=45, m=2) | **Accepted（現行最良）** | `python3 tools/fbverify.py solutions/02_fable_47.vsm` |
| `00_baseline_93.vsm` | 93 (j=91, m=2) | Accepted（旧最良） | `python3 tools/fbverify.py solutions/00_baseline_93.vsm` |
| `01_nearmiss_92.vsm` | 92 | 22 バイト不一致（DRAM word 0..2） | 公式 judge: `32744 correct / 22 mismatch` |

`01_nearmiss_92.vsm` は `research/experiments/constants/del_18.vsm`（`imm i"32" $r25` を削除）。
定数 32 を 1 語増やさずに生成する手段は全数探索で見つかっていない（`research/hypotheses.md` H5）。

`02_fable_47.vsm` は `research/experiments/fable52/v15_47_commented.vsm`（注釈・列そろえ版。命令は `v15_47.vsm` と同じ）。
生成元は同ディレクトリの `jopt.py`（CP-SAT）と数式モデル `model14.py`。

目標の `52` 以下は達成済み。候補は `tools/fbcheck.py` で高速に落とし、`tools/fbverify.py`（公式 judge、1.5 秒）で確定する。
