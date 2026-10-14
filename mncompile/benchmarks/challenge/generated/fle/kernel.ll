; ModuleID = '<stdin>'
source_filename = "<stdin>"

define float @threshold(float %x) {
  %mask = fcmp oge float %x, 1.000000e+00
  %selected = select i1 %mask, float 0x7FF0000000000000, float 0.000000e+00
  ret float %selected
}
