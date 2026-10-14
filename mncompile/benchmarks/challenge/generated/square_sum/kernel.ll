; ModuleID = '<stdin>'
source_filename = "<stdin>"

define double @square(double %x) {
  %v = fmul double %x, %x
  ret double %v
}
