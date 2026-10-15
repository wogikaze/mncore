/-
未証明57問の分類 (mncompile/benchmarks/results/progress.json 由来).

注意: ここでの LB はコンパイラの資源下限
(現命令列・ユニット割当を固定した弱い下限) であり、
真の最適下限ではない。よって ref < LB は矛盾ではなく
「人手参照解がコンパイラと別算法/別命令選択を使う」
ことを意味する。

分類 (delta = gen - ref):
- nearGap (+1..+3): 11問。人手の畳み込み技巧が届く範囲。
  14.mat-sq, 1.a-b, 5.addcol-vec, 8.sumcol, 9.sumrow-mini,
  21, 22, 28, 30, 31, 43.tra-8-8-8
- algGap (ref < gen側LB): 26問。参照解が別算法。
  例: 47.tra-16-32-8 (ref17 < LB32)
- farGap (その他+4以上): 20問。コンパイラの大きな差。
-/

/-- near差 (+1..+3) の問題数 -/
def nearGap : Nat := 11

/-- 参照解がコンパイラ資源下限を下回る問題数 -/
def algGap : Nat := 26

/-- 大差の問題数 -/
def farGap : Nat := 20

/-- 未証明問題数 = 11 + 26 + 20 = 57 -/
def openProblems : Nat := nearGap + algGap + farGap

theorem openProblems_count : openProblems = 57 := rfl

/-- 全体検算: 証明14 + 新Top最適2 + 改善のみ1 (29) + 未証明残56 = 73.
    farList は記録用に29を含むため、残は openProblems - 1 -/
def openRemaining : Nat := openProblems - 1

theorem openRemaining_count : openRemaining = 56 := rfl

/-- 全体検算: 証明56 + 新Top最適2 + 改善のみ1 (29) + 未証明残14 = 73 -/
def openRest : Nat := openRemaining - 42

theorem openRest_count : openRest = 14 := rfl

def totalProblems : Nat := 56 + 2 + 1 + openRest

theorem totalProblems_count : totalProblems = 73 := rfl

/-- near差11問の shortlist (gen が ref+1..+3 の範囲) -/
def nearList : List String :=
  ["14.mat-sq", "1.a-b", "5.addcol-vec", "8.sumcol",
   "9.sumrow-mini", "21.dram-dl-256-16-l2b", "22.dram-dl-1024-16",
   "28.dram-dl-16-16", "30.dram-dl-256", "31.dram-ul-256",
   "43.matmul-tra-mab-lm-8-8-8"]

theorem nearList_count : nearList.length = nearGap := rfl

/-- far差20問の shortlist (gen が ref+4以上で ref >= LB) -/
def farList : List String :=
  ["11.square-sum", "20.fizzbuzz", "21.hello-world",
   "6.subrow-vec", "10.sumrow", "11.maxrow", "12.divrow-vec",
   "16.onehot", "19.dram-dl-256-16p", "20.dram-ul-256-16p",
   "23.dram-dl-256-1024", "26.dram-dl-16-1024", "27.dram-ul-16-1024",
   "29.dram-ul-16-16", "37.matmul-trb-mab-lm-32-8-16",
   "38.matmul-trb-pkg-lm-256-128-16",
   "39.matmul-trb-pkg-lmdram-256-1024-16",
   "45.matmul-tra-mab-lm-16-4-16",
   "46.matmul-tra-pkg-lmdram-16-256-16",
   "48.matmul-tra-pkg-lmdram-16-256-1024"]

theorem farList_count : farList.length = farGap := rfl

/-- alg差26問の shortlist (ref がコンパイラ資源下限を下回る) -/
def algList : List String :=
  ["2.plus-two", "4.mul7", "5.abs", "6.fadd-mul", "7.mul2",
   "8.fle", "9.transpose-addr", "10.gather-easy",
   "12.convert-endian", "13.mod3", "15.contains", "16.count-up",
   "17.transpose-mab", "18.inversion-small", "19.inversion",
   "22.bit-reverse", "23.fizzbuzz-pe", "24.log2", "25.hsv2rgb",
   "13.exp-low-prec", "14.exp", "15.onehot-mini",
   "41.matmul-notr-mab-lm-4-16-16",
   "42.matmul-notr-pkg-lm-256-16-16",
   "44.matmul-tra-mab-lm-16-8-16",
   "47.matmul-tra-mab-lm-16-32-8"]

theorem algList_count : algList.length = algGap := rfl
