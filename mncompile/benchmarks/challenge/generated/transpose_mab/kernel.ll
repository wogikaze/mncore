; ModuleID = '<stdin>'
source_filename = "<stdin>"

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.abs.i64(i64, i1 immarg) #0

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.ctlz.i64(i64, i1 immarg) #0

define i64 @kernel(i64 %index) {
  %v0 = shl i64 %index, 4
  %v1 = and i64 %v0, 240
  %v2 = lshr i64 %index, 4
  %v3 = or i64 %v1, %v2
  ret i64 %v3
}

attributes #0 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
