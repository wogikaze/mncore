; ModuleID = '<stdin>'
source_filename = "<stdin>"

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.abs.i64(i64, i1 immarg) #0

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.ctlz.i64(i64, i1 immarg) #0

define i64 @kernel(i64 %x) {
  %v0 = add i64 %x, 2
  ret i64 %v0
}

attributes #0 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
