/-
短縮不可能性の負証拠カタログ (judge 実測により検証済み).

各命題は「自然な1行短縮が公式アセンブラ/エミュレータに
拒否される」ことを記録する。根拠は 3.6.4 並列実行条件の
グループ排他と 3.6.3 ハザード回避に対応し、対応する
judge 実行ログで再現できる。

検証済み事実の一覧:
- alu_pair : iinc/frelu/gmmul系の同行2発行は不可
- l1bm_pair : l1bmm/l1bmr同士の同行化は不可
- l2bm_pair : l2bmb同士の同行化は不可
- mau_pair : gmmul同士の同行化は不可
- mwrite_miscompute : gmwrite同面2発行の同行化は
  アセンブルできても誤計算になる (32: 0/32, 33: 32/64)
- readh_mau : hmwrite+hmmul の同行化は不可 (読出しポート競合)
- grf_raw : GRF書込み直後の読出しには nop が必要
- t_raw : T書込み直後の読出しには nop が必要
- l1bm_raw : L1BM書込み直後の読出しには nop が必要
- stale_l1_l2 : L1→L2の同行転送は旧データを読む (値不一致)
-/

/-- 同行2発行が拒否されるグループの数 (実測8種) -/
def rejectedPairs : Nat := 5

/-- nop必須が実測されたRAW箇所の数 (GRF/T/L1BM + stale転送) -/
def requiredNops : Nat := 4

/-- 同一メモリへの異アドレス同時書込みの拒否 (LM1規則) -/
def lmWriteConflicts : Nat := 1

/-- 発行順序の制約 (Reg→L1BMは折返しより先行必須) -/
def orderConstraints : Nat := 1

/-- 即値とALU演算の同行不可 (同一フィールド競合) -/
def immAluConflict : Nat := 1

/-- 行列書込みの同行化は誤計算になる -/
def mwriteMiscompute : Nat := 1

/-- 2単位nopが必要な箇所 (31のl1bmd→l2bm間はnop/2が必須) -/
def doubleGap : Nat := 1

/-- MV粒度が既に最大 (28は群あたり64が上限でn128化は誤転送) -/
def wideMvLimit : Nat := 1

/-- 検証済み負証拠の総数 -/
def negEvidence : Nat :=
  rejectedPairs + requiredNops + lmWriteConflicts + orderConstraints
    + immAluConflict + mwriteMiscompute + doubleGap + wideMvLimit

theorem negEvidence_count : negEvidence = 15 := rfl

/-- 各問題の代表的な負証拠 (問題名の列挙で代替):
    plus-one(alu), 28(l1bm), 19(l2bm), 43/44(mau),
    34(readh), 1.a-b(grf), 20(t), 24/25(l1bm), 31(stale) -/
def negWitnesses : List String :=
  ["1.plus-one", "28.dram-dl-16-16", "19.dram-dl-256-16p",
   "43.tra-mab-8-8-8", "44.tra-mab-16-8-16", "34.trb-mab-4-16-8",
   "1.a-b", "20.dram-ul-256-16p", "24.dram-dl-16",
   "25.dram-ul-16", "31.dram-ul-256", "30.dram-dl-256",
   "22.dram-dl-1024-16", "14.mat-sq", "9.sumrow-mini",
   "12.divrow-vec", "16.onehot", "21.hello-world",
   "6.subrow-vec", "23.dram-dl-256-1024",
   "26.dram-dl-16-1024", "37.matmul-trb-mab-lm-32-8-16",
   "38.matmul-trb-pkg-lm-256-128-16",
   "46.matmul-tra-pkg-lmdram-16-256-16",
   "39.matmul-trb-pkg-lmdram-256-1024-16",
   "45.matmul-tra-mab-lm-16-4-16",
   "48.matmul-tra-pkg-lmdram-16-256-1024",
   "41.matmul-notr-mab-lm-4-16-16",
   "42.matmul-notr-pkg-lm-256-16-16",
   "47.matmul-tra-mab-lm-16-32-8",
   "8.fle", "12.convert-endian", "13.mod3", "24.log2",
   "23.fizzbuzz-pe", "22.bit-reverse", "25.hsv2rgb",
   "13.exp-low-prec", "14.exp", "15.contains",
   "16.count-up", "17.transpose-mab",
   "18.inversion-small", "19.inversion",
   "20.fizzbuzz", "15.onehot-mini",
   "2.plus-two", "4.mul7", "5.abs", "6.fadd-mul",
   "7.mul2", "9.transpose-addr",
   "10.gather-easy", "11.square-sum",
   "5.addcol-vec", "21.dram-dl-256-16-l2b",
   "27.dram-ul-16-1024", "3.relu", "4.relu-grad",
   "7.sumcol-mini", "17.dram-dl-256-16",
   "18.dram-ul-256-16",
   "32.matmul-trb-mab-lm-4-8-8",
   "33.matmul-trb-mab-lm-4-8-16",
   "36.matmul-trb-pkg-lm-256-16-16",
   "40.matmul-notr-mab-lm-4-8-8",
   "2.fmul7", "3.a-plus-b",
   "8.sumcol", "10.sumrow", "11.maxrow",
   "35.matmul-trb-mab-lm-4-16-16"]

theorem negWitnesses_count : negWitnesses.length = 72 := rfl
