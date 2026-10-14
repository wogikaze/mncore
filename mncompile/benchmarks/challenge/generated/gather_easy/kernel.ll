; ModuleID = '<stdin>'
source_filename = "<stdin>"

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.abs.i64(i64, i1 immarg) #0

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.ctlz.i64(i64, i1 immarg) #0

define i64 @word_address(i64 %index) {
  %v0 = shl i64 %index, 1
  ret i64 %v0
}

attributes #0 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }


define double @gather(ptr %row, i64 %index) {
  %p = getelementptr double, ptr %row, i64 %index
  %v = load double, ptr %p, align 8
  ret double %v
}
