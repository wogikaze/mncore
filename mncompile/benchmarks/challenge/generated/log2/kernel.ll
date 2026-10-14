; ModuleID = '<stdin>'
source_filename = "<stdin>"

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i32 @llvm.abs.i32(i32, i1 immarg) #0

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i32 @llvm.ctlz.i32(i32, i1 immarg) #0

define i32 @kernel(i32 %x) {
  %v0 = call i32 @llvm.ctlz.i32(i32 %x, i1 false), !range !0
  %v2 = sub nsw i32 31, %v0
  ret i32 %v2
}

attributes #0 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }

!0 = !{i32 0, i32 33}
