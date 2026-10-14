; ModuleID = '<stdin>'
source_filename = "<stdin>"

define i32 @inversion_term(i32 %left, i32 %right) {
  %v = icmp ugt i32 %left, %right
  %n = zext i1 %v to i32
  ret i32 %n
}
