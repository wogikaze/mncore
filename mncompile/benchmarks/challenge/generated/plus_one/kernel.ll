; ModuleID = '<stdin>'
source_filename = "<stdin>"

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i32 @llvm.abs.i32(i32, i1 immarg) #0

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i32 @llvm.ctlz.i32(i32, i1 immarg) #0

define i32 @kernel(i32 %x) {
  %v0 = add i32 %x, 1
  ret i32 %v0
}

attributes #0 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
