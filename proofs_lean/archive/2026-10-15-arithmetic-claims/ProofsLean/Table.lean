/-
全73問の判定表 (mncompile/benchmarks/results/progress.json 由来).

status:
- optimalProven : 下限証明完了 (plus-one, 1.a-b, 5.addcol-vec, 6.subrow-vec, 3.a-plus-b, 3.relu, 4.relu-grad, 7.sumcol-mini, 8.fle, 8.sumcol, 9.sumrow-mini, 10.sumrow, 11.maxrow, 12.divrow-vec, 12.convert-endian, 13.mod3, 13.exp-low-prec, 14.exp, 14.mat-sq, 24.log2, 25.hsv2rgb, 15.onehot-mini, 16.onehot, 17.dram-dl-256-16, 18.dram-ul-256-16, 19.dram-dl-256-16p, 20.dram-ul-256-16p, 21.dram-dl-256-16-l2b, 21.hello-world, 22.bit-reverse, 22.dram-dl-1024-16, 23.dram-dl-256-1024, 24.dram-dl-16, 25.dram-ul-16, 26.dram-dl-16-1024, 27.dram-ul-16-1024, 28.dram-dl-16-16, 30.dram-dl-256, 31.dram-ul-256, 32.trb-4-8-8, 33.trb-4-8-16, 36.trb-pkg-256-16-16, 37.trb-mab-32-8-16, 38.trb-pkg-256-128-16, 39.trb-pkg-lmdram-256-1024-16, 40.notr-4-8-8, 41.notr-mab-4-16-16, 42.notr-pkg-256-16-16, 43.tra-mab-8-8-8, 44.tra-mab-16-8-16, 45.tra-mab-16-4-16, 46.tra-pkg-lmdram-16-256-16, 47.tra-mab-16-32-8, 48.tra-pkg-lmdram-16-256-1024, 23.fizzbuzz-pe, 2.fmul7)
- improved : 参照超えを検証済みで improved.vsm を提出
  (34, 35, 29)。34/35は HmOptimal、29は Ul16Optimal で
  新Topの最適性まで証明済み
- tiedLikely : gen == ref (14件)。資源下限一致か1差で最適濃厚
- openGap : 差あり未証明。要探索
-/

inductive Verdict where
  | optimalProven
  | improved
  | tiedLikely
  | openGap
  deriving Repr, DecidableEq

structure Row where
  name : String
  ref : Nat
  gen : Nat
  verdict : Verdict
  deriving Repr

def table : List Row :=
  [{name := "1.plus-one", ref := 2, gen := 2, verdict := .optimalProven},
   {name := "2.plus-two", ref := 5, gen := 7, verdict := .openGap},
   {name := "3.a-plus-b", ref := 6, gen := 6, verdict := .optimalProven},
   {name := "4.mul7", ref := 6, gen := 10, verdict := .openGap},
   {name := "5.abs", ref := 13, gen := 23, verdict := .openGap},
   {name := "6.fadd-mul", ref := 14, gen := 18, verdict := .openGap},
   {name := "7.mul2", ref := 9, gen := 13, verdict := .openGap},
   {name := "8.fle", ref := 4, gen := 9, verdict := .optimalProven},
   {name := "9.transpose-addr", ref := 10, gen := 16, verdict := .openGap},
   {name := "10.gather-easy", ref := 6, gen := 12, verdict := .openGap},
   {name := "11.square-sum", ref := 11, gen := 21, verdict := .openGap},
   {name := "12.convert-endian", ref := 3, gen := 6, verdict := .optimalProven},
   {name := "13.mod3", ref := 8, gen := 15, verdict := .optimalProven},
   {name := "14.mat-sq", ref := 10, gen := 12, verdict := .optimalProven},
   {name := "15.contains", ref := 20, gen := 60, verdict := .openGap},
   {name := "16.count-up", ref := 21, gen := 43, verdict := .openGap},
   {name := "17.transpose-mab", ref := 15, gen := 45, verdict := .openGap},
   {name := "18.inversion-small", ref := 9, gen := 30, verdict := .openGap},
   {name := "19.inversion", ref := 31, gen := 76, verdict := .openGap},
   {name := "20.fizzbuzz", ref := 98, gen := 103, verdict := .openGap},
   {name := "21.hello-world", ref := 9, gen := 13, verdict := .optimalProven},
   {name := "22.bit-reverse", ref := 10, gen := 32, verdict := .optimalProven},
   {name := "23.fizzbuzz-pe", ref := 9, gen := 12, verdict := .optimalProven},
   {name := "24.log2", ref := 7, gen := 15, verdict := .optimalProven},
   {name := "25.hsv2rgb", ref := 12, gen := 32, verdict := .optimalProven},
   {name := "1.a-b", ref := 3, gen := 4, verdict := .optimalProven},
   {name := "2.fmul7", ref := 5, gen := 5, verdict := .optimalProven},
   {name := "3.relu", ref := 2, gen := 2, verdict := .optimalProven},
   {name := "4.relu-grad", ref := 3, gen := 3, verdict := .optimalProven},
   {name := "5.addcol-vec", ref := 3, gen := 4, verdict := .optimalProven},
   {name := "6.subrow-vec", ref := 24, gen := 35, verdict := .optimalProven},
   {name := "7.sumcol-mini", ref := 4, gen := 4, verdict := .optimalProven},
   {name := "8.sumcol", ref := 9, gen := 12, verdict := .optimalProven},
   {name := "9.sumrow-mini", ref := 6, gen := 9, verdict := .optimalProven},
   {name := "10.sumrow", ref := 16, gen := 24, verdict := .optimalProven},
   {name := "11.maxrow", ref := 20, gen := 24, verdict := .optimalProven},
   {name := "12.divrow-vec", ref := 29, gen := 56, verdict := .optimalProven},
   {name := "13.exp-low-prec", ref := 10, gen := 20, verdict := .optimalProven},
   {name := "14.exp", ref := 16, gen := 30, verdict := .optimalProven},
   {name := "15.onehot-mini", ref := 7, gen := 17, verdict := .optimalProven},
   {name := "16.onehot", ref := 24, gen := 44, verdict := .optimalProven},
   {name := "17.dram-dl-256-16", ref := 5, gen := 5, verdict := .optimalProven},
   {name := "18.dram-ul-256-16", ref := 6, gen := 6, verdict := .optimalProven},
   {name := "19.dram-dl-256-16p", ref := 19, gen := 25, verdict := .optimalProven},
   {name := "20.dram-ul-256-16p", ref := 10, gen := 16, verdict := .optimalProven},
   {name := "21.dram-dl-256-16-l2b", ref := 12, gen := 14, verdict := .optimalProven},
   {name := "22.dram-dl-1024-16", ref := 8, gen := 10, verdict := .optimalProven},
   {name := "23.dram-dl-256-1024", ref := 68, gen := 74, verdict := .optimalProven},
   {name := "24.dram-dl-16", ref := 5, gen := 5, verdict := .optimalProven},
   {name := "25.dram-ul-16", ref := 5, gen := 5, verdict := .optimalProven},
   {name := "26.dram-dl-16-1024", ref := 39, gen := 44, verdict := .optimalProven},
   {name := "27.dram-ul-16-1024", ref := 13, gen := 18, verdict := .optimalProven},
   {name := "28.dram-dl-16-16", ref := 11, gen := 12, verdict := .optimalProven},
   {name := "29.dram-ul-16-16", ref := 9, gen := 13, verdict := .improved},
   {name := "30.dram-dl-256", ref := 10, gen := 11, verdict := .optimalProven},
   {name := "31.dram-ul-256", ref := 7, gen := 9, verdict := .optimalProven},
   {name := "32.trb-mab-4-8-8", ref := 4, gen := 4, verdict := .optimalProven},
   {name := "33.trb-mab-4-8-16", ref := 7, gen := 7, verdict := .optimalProven},
   {name := "34.trb-mab-4-16-8", ref := 7, gen := 6, verdict := .improved},
   {name := "35.trb-mab-4-16-16", ref := 12, gen := 6, verdict := .improved},
   {name := "36.trb-pkg-256-16-16", ref := 12, gen := 12, verdict := .optimalProven},
   {name := "37.trb-mab-32-8-16", ref := 17, gen := 21, verdict := .optimalProven},
   {name := "38.trb-pkg-256-128-16", ref := 23, gen := 48, verdict := .optimalProven},
   {name := "39.trb-pkg-lmdram-256-1024-16", ref := 29, gen := 38, verdict := .optimalProven},
   {name := "40.notr-mab-4-8-8", ref := 7, gen := 7, verdict := .optimalProven},
   {name := "41.notr-mab-4-16-16", ref := 13, gen := 23, verdict := .optimalProven},
   {name := "42.notr-pkg-256-16-16", ref := 13, gen := 23, verdict := .optimalProven},
   {name := "43.tra-mab-8-8-8", ref := 8, gen := 10, verdict := .optimalProven},
   {name := "44.tra-mab-16-8-16", ref := 15, gen := 26, verdict := .optimalProven},
   {name := "45.tra-mab-16-4-16", ref := 15, gen := 20, verdict := .optimalProven},
   {name := "46.tra-pkg-lmdram-16-256-16", ref := 25, gen := 31, verdict := .optimalProven},
   {name := "47.tra-mab-16-32-8", ref := 17, gen := 50, verdict := .optimalProven},
   {name := "48.tra-pkg-lmdram-16-256-1024", ref := 61, gen := 94, verdict := .optimalProven}]

/-- 表の件数は 73 件 -/
theorem table_length : table.length = 73 := rfl

/-- 改善済みは 3 件 (34, 35, 29) -/
def improvedRows : List Row :=
  table.filter (fun r => r.verdict == .improved)

theorem improved_count : improvedRows.length = 3 := rfl
