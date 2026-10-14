; ModuleID = '<stdin>'
source_filename = "<stdin>"

define i32 @classify(i32 %x) {
  %r15 = urem i32 %x, 15
  %p15 = icmp eq i32 %r15, 0
  %r3 = urem i32 %x, 3
  %p3 = icmp eq i32 %r3, 0
  %r5 = urem i32 %x, 5
  %p5 = icmp eq i32 %r5, 0
  %tail = select i1 %p5, i32 48059, i32 %x
  %mid = select i1 %p3, i32 65535, i32 %tail
  %result = select i1 %p15, i32 -17477, i32 %mid
  ret i32 %result
}
