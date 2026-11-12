from fl import run
# omr1 := all ones (positive), omr2 := pattern (hi+, lo-), then write omr1 with flags all-zero (negative) under write-mask omr2
for wm in ['$imr2','$llimr2']:
  for op in ['hvpassa','fvpassa']:
    prog=f'''imm ui"0x3c003c00" $nowrite
hvpassa $aluf $omr1
imm ui"0x3c00bc00" $nowrite
hvpassa $aluf $omr2
imm ui"0xbc00bc00" $nowrite
{op} $aluf $omr1/{wm}
imm ui"0x11111111" $ln0v
nop
nop
imm ui"0xFFFFFFFF" $ln0v/$imr1
'''
    print(wm,op,run(prog))
