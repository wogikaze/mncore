# 下界（予備解析。Lean 証明ではない）

> このファイルの内容は `research/preliminary/fizzbuzz-delivery/` の解析に基づく予備結果であり、
> Lean で検証されていない。CP-SAT の UNSAT は Lean の定理ではない。
# 下界証明

## LB1: FizzBuzz 最終配送（全 ISA、範囲限定）— 証明済み

- **主張**: 4096 個の出力長語が PE 側ストレージに揃っており、他は全てゼロという状態から、
  Group 0 DRAM 0..4095 に置くには **8 語以上**必要。かつ **8 語で達成可能（tight）**。
- **系**: 出力を生成する任意のプログラムは **j+m ≥ 9**。
- **内訳**: `l1bmd` + nop×2（ハザード必須）+ `l2bmd`×2 + nop + `mvd/n512` + `mvp/n4096`。
- **達成例**: 受理済み 93 語解の最終 8 語（j=6, m=2）がまさにこの鎖。
- **検証**:
  - `bash research/preliminary/fizzbuzz-delivery/verify.sh` → `ALL VERIFICATION STEPS PASSED`（親エージェントが実行）
  - `python3 research/preliminary/fizzbuzz-delivery/delivery_model.py --check`: 全 6^7 行動列の総当たりで K=7 は NO PLAN、
    CP-SAT で K=7 INFEASIBLE（timeout ではない、0.002s）、K=8 OPTIMAL。
- **適用範囲外**: 値の計算コスト。52 語目標に対しては `j+m ≥ 9` 以上のことは言わない。
- **仮定**: DRAM/PDM/SRAM ゼロ初期化（judge は `--offchip-memory-init zero`、`--dirty` なし）、
  `d set` なし、公式 assemble3 のハザード規則。

## LB2: DRAM 書き込み帯域（自明に潰れる）

1 命令語で最大 `mvp/n16384` = 16384 長語 = 131072 バイト。`ceil(32766/131072)=1`。
**帯域は律速ではない**。律速のホップは L1BM→L2BM の `l2bmd`（1 語 16384 バイト）。

## 未解決

- 値計算（ALU 式 1 本/語、93 語解で 66 本）に対する下界は未証明。
- 52 語の達成可能性は未決定。
