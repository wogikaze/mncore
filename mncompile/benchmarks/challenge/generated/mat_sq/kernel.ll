; ModuleID = '<stdin>'
source_filename = "<stdin>"

define i32 @matrix_term(float %a, float %b) {
  %x = fptoui float %a to i32
  %y = fptoui float %b to i32
  %p = mul i32 %x, %y
  ret i32 %p
}
