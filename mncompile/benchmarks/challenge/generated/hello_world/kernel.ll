; ModuleID = '<stdin>'
source_filename = "<stdin>"

@data = private constant [13 x i8] c"Hello, world!"

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias nocapture writeonly, ptr noalias nocapture readonly, i64, i1 immarg) #0

define void @kernel(ptr %output) {
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 1 dereferenceable(13) %output, ptr noundef nonnull align 1 dereferenceable(13) @data, i64 13, i1 false)
  ret void
}

attributes #0 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
