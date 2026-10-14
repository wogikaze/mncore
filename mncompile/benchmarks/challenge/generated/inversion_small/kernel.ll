; ModuleID = '<stdin>'
source_filename = "<stdin>"

define i64 @inversion_term(i64 %left, i64 %right) {
  %v = icmp ugt i64 %left, %right
  %n = zext i1 %v to i64
  ret i64 %n
}
