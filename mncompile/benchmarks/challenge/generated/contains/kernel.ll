; ModuleID = '<stdin>'
source_filename = "<stdin>"

define i64 @membership_term(i64 %query, i64 %candidate) {
  %equal = icmp eq i64 %query, %candidate
  %value = zext i1 %equal to i64
  ret i64 %value
}
