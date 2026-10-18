# 06 — ユニット内訳と 53 行への削減計画（round 3）

`mncompile.machine.parse_program` で main.vsm を分類した確定値:

| unit | 数 |
|---|---|
| alu | 66 |
| mau | 41 |
| mwrite | 1 (dmwrite) |
| mread | 1 (dmread) |
| l1bm | 1 |
| l2bm | 2 |
| mv | 2 |
| nop | 8 |

行数 93。ALU は 1 行 1 命令なので **ALU 66 が律速**。53 行には ALU ≤ 51 が必要。

## ALU 66 の内訳

| ステージ | 行 | ALU 数 |
|---|---|---|
| 座標→r0/s0 構築 | 1,4–13,16 | 12 |
| imm 定数 | 2,3,14,15,18–20,22,23,26–31,34,36,48,49,52,54–56,78 | 24 |
| est/桁/選択 | 24,25,32,33,35,37–39,42–47,51,53 | 16 |
| canvas 結合 (ipassa/ladd/lpassa) | 57–59,62,66,70,73,77 | 8 |
| 最終 pack (shift/or) | 79–84 | 6 |

削減案: imm 24→12 (-12)、pack 6→3 (-3) で ALU 51。これが最短ルート。

## 新しく判明した制約

- **即値命令と LM0 アクセスは同一行に置けない**（アセンブラが
  `Instruction field conflict detected between 'immediate' and 'lm0'` で拒否）。
  canvas 書き込み (`$mt[...]` = LM0 + T 間接) を imm 行へ移す案は全滅。
- `$mt[...]` の T は L1 `ipackbit $subpeid $llt` の値（= subpeid）で、L77
  `lpassa $lr18 $llt` で「最終 8 バイトのシフト量」に差し替えられる。
  canvas 書き込み中に T を壊す再配置は不可。
- `ipassa` を `fvpassa` に変えて MAU 化する案は、ホスト行が全て
  imm（LM0 禁止）か既に mau-calc 持ちで、載せ替え先が無い。

## 現実的な順序

1. imm のうち float 定数（63, 1/63, 1/71, 1/79, 0.1, 0.01, 0.001, 0x4b0000xx）を
   MAU 演算で生成し、ALU 行を消す。生成 op は LM0 に触れない行へ載せる。
2. canvas の 16 バイトを 2 長語として直接組み、pack を 3 ALU に。
3. 残りを再スケジュール（asm→fastsim→judge）。
