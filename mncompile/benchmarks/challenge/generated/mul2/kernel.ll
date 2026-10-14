; ModuleID = '<stdin>'
source_filename = "<stdin>"

define double @kernel(double %x) {
entry:
  %v0 = fmul double %x, 2.000000e+00
  ret double %v0
}
