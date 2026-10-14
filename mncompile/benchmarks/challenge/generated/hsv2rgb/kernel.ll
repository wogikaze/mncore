; ModuleID = '<stdin>'
source_filename = "<stdin>"

define float @hsv_p(float %s, float %v) {
  %a = fsub float 1.000000e+00, %s
  %p = fmul float %a, %v
  ret float %p
}

define float @hsv_q(float %s, float %v, float %f) {
  %a = fmul float %s, %f
  %b = fsub float 1.000000e+00, %a
  %q = fmul float %b, %v
  ret float %q
}

define float @hsv_t(float %s, float %v, float %f) {
  %a = fsub float 1.000000e+00, %f
  %b = fmul float %a, %s
  %c = fsub float 1.000000e+00, %b
  %t = fmul float %c, %v
  ret float %t
}
