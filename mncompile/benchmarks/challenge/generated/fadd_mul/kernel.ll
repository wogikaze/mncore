; ModuleID = '<stdin>'
source_filename = "<stdin>"

define double @kernel(double %x) {
entry:
  %v0 = fadd double %x, 8.000000e+00
  %v1 = fmul double %v0, 8.000000e+00
  ret double %v1
}
