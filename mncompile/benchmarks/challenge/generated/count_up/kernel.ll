; ModuleID = '<stdin>'
source_filename = "<stdin>"

define void @arange(ptr %output) {
entry:
  br label %loop

loop:                                             ; preds = %loop, %entry
  %i = phi i32 [ 1, %entry ], [ %next, %loop ]
  %index = add i32 %i, -1
  %wide = zext i32 %index to i64
  %p = getelementptr i32, ptr %output, i64 %wide
  store i32 %i, ptr %p, align 4
  %next = add i32 %i, 1
  %done = icmp eq i32 %i, 32768
  br i1 %done, label %exit, label %loop

exit:                                             ; preds = %loop
  ret void
}
