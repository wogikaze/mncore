; ModuleID = '<stdin>'
source_filename = "<stdin>"

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.bitreverse.i64(i64) #0

define i64 @reverse_bits(i64 %x) {
  %v = call i64 @llvm.bitreverse.i64(i64 %x)
  ret i64 %v
}

define i64 @reverse_index(i64 %i) {
  %v = sub i64 15, %i
  ret i64 %v
}

attributes #0 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
