# dram_dl_16_1024 — 38-line attempt (scratch/mnist_golf2)

結論: **38 行は不可能**。公式アセンブラのハザード規則 (SDM 3.6.3.6, L2BM→L1BM 書込みの
7 cycle 後にしか L1BM→PE 読み出しできない) と、1 行 1 `l2bmd` / 1 行 1 `l1bmd` という
命令発行制約の下で、下記の下限証明が成り立つ。最良は既存の 39 行。

## 現状

- `problems/26.dram-dl-16-1024/answer.vsm` = 39 行 (j=34, m=5) ACCEPTED。
- 資源下限: `mvp`×4 + `mvb`×1 = 5 m、`l2bmd`×32、`l1bmd`×4。
  - `l2bmd` 1 命令 = 256 長語 (8 L1B × 32) なので 8192/256 = 32。
  - `l1bmd` 1 命令 = 4 長語/PE × 64 PE = 256 長語/L1B なので 1024/256 = 4。
  - MV 5: PDM に 4 DRAM グループを 2048 語ずつ連結するには `mvp`×4 が必要で、
    その PDM を全 L2BM へ放送する `mvb`×1。`mvd`/`mvb4`/直接 `mvb` は 16 語
    グループ交互配置になり、`l2bmd` の 8 語分配と両立しない (下記の代数で証明)。
- 41 命令語 = 32 `l2bmd` + 4 `l1bmd` + 5 MV。

## 38 行が不可能な理由 (証明)

38 行 = m + j。m ≥ 5 なので j ≤ 33。j 行は各 1 `l2bmd` (同一行に 2 つの `l2b` 命令は
`Instruction field conflict` で不可) と、`l2bmd` 行に融合できる `l1bmd` (1 行 1 つ、
2 つは `l1bm_emit` の field conflict) からなる。よって

- 32 個の実 `l2bmd` 行のうち最遅のものが j 位置 p ≥ 32 を占める
  (j ≤ 33 で 32 行必要だから)。
- その行が書くチャンク (32 語) の領域を読む `l1bmd` は p より後、かつ
  7 cycle 規則により **2 行以上後** に必要 (1 行後は不可、下記)。
- しかし j ≤ 33 では p+2 ≥ 34 に置けず、同一行 (p) に融合するとエミュレータは
  そのステップ前の状態を読むため、そのチャンクが 0 のまま (1024 値不一致)。

1 行後が必ず違反すること: `l2bmd` は 32 語をサイクル 0..3 に 8 語ずつ書く。
`l1bmd` は 64 語を 1 サイクルで読む。チャンク末尾 8 語 (cw=3) を読むサイクル cr は
0..3 で、距離 = (p+1)*4+cr - (p*4+3) = cr+1 ≤ 4 < 7。したがって 1 行後は常に
DataRaceError。2 行後ならチャンクが読み出しサイクル 3 に入る場合だけ距離 ≥ 8 で
合法 (既存 39 行解の最終 `l1bmd` がこれ)。

### 検証 (実測)

| candidate | lines | assembler | judge |
|---|---|---|---|
| `answer.vsm` (baseline) | 39 | OK (j=34,m=5) | ACCEPTED score=39 |
| `cand1_38.vsm` | 38 | OK (j=33,m=5) | 31744 correct / **1024 mismatch** (最終チャンクが 0 のまま) |
| `cand2_38_hazard_correct.vsm` | 38 | **DataRaceError (L1BM 448, line 39)** | (参考) hazard checker 無効なら ACCEPTED score=38 |
| 既存 cand3 / cand9 | 38 | DataRaceError | — |
| 既存 cand5/6/7 (MV 削減) | 35-36 | OK | 32640 mismatch (16 語交互配置) |

`cand2` は「数値的には正しいが 1 行早い」スケジュールで、公式アセンブラのハザード
チェッカだけが拒否する。`--disable-hazard-checker` を付けた診断実行では
`ACCEPTED!! score=38 j=33 m=5` になる。つまり残る障害はデータ依存ではなく
SDM 3.6.3.6 の 7 cycle 規則そのもの。

## 試して駄目だった逃げ道

- 最終 `l2bmd` を重複書込み (同じチャンクを 2 回) にして `l1bmd` を同一行へ:
  33 `l2bmd` (32 実 + 1 重複) + 4 融合 = 33 j 行にはなるが、最遅の実チャンクが
  位置 37 に残り、その領域の `l1bmd` は 2 行後 (39 行目) が必要。
  重複行を最終行に置いても、直前行の実チャンクとの 7 cycle 規則は回避できない。
- 最終チャンクを読取り窓の外へ (未使用 L1BM アドレスへ) 書く: データ欠落。
- `l2bmd@<L1B set>` で一部 L1B のみ書く: `l1bmd` は全 L1B を読むため
  書いた L1B で必ず 7 cycle 違反。
- 2 `l2bmd` / 2 `l1bmd` を 1 行に: field conflict。
- `nop`/`noforward`/`wait`: すべて j 行として数えられ、無料のギャップにはならない。
- `l1bmd` の 2 長語デスティネーション (`$llm`): `Word size of L1BM distribution
  destinations must not be double-long` で拒否。
- `l1bmd+/-mabdiff` で窓をずらす: 読取りアドレスは変わらず (チェッカも同じ)、
  また 8 語シフトを mabdiff で厳密に補正できない (64 語ブロック境界で折返し)。
- `l1bmm`/`l1bmm4` (MAB 放送) で `l1bmd` を置換: 16 MAB は別々の列を持つため不可。
- MV 4 本: PDM に 4 グループを連結するには `mvp` 4 本が必要。`mvd` は 16 語交互、
  `mvp` 並列形は PDM グループが分かれる、`mvb` は PDM 1 グループしか読まない。
- L2BM の 16 語交互配置を `l2bmd` の source アドレスで補正: L2BM ブロック内で
  グループ g は 16 語単位、`l2bmd` は 8 語単位で分配するため、必要チャンクの
  4 サイクル分 (M の 4×64 語) を 1 命令で揃えられない (代数で不一致)。

## 成果物

- `cand1_38.vsm` — 38 行。組立可、1024 値不一致 (最小の near-miss)。
- `cand2_38_hazard_correct.vsm` — 38 行。数値は正しいが 7 cycle 規則違反で組立不可。
- `probe_same_line/` — 同一行 l2bmd→l1bmd がステップ前状態を読むこと、および
  1/2/3 行ギャップの可否の実測。
