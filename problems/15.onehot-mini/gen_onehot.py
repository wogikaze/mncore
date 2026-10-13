import sys

lines = [
    'imm i"0" $s0',
    'imm i"1" $s1',
    'imm i"8" $s2',
    'imm i"9" $s3',
    'imm f"1.0" $s15',
    'imm f"0.0" $s14',
    'nop/4',
    'fpassa $s14 $n0v512',
    'nop/4'
]

for i in range(64):
    # Load T[i] into r10/r11 (aligned longword load)
    lines.append(f'lpassa $lm{i & ~1} $lr10/1000')
    lines.append('nop/4')
    
    t_reg = 10 if i % 2 == 0 else 11
    
    for col_val in [0, 1, 8, 9]:
        s_reg = {0:0, 1:1, 8:2, 9:3}[col_val]
        col_off = {0:0, 1:1, 8:4, 9:5}[col_val]
        
        # Compare T[i] with column value
        lines.append(f'ixor $r{t_reg} $s{s_reg} $omr1/1111')
        lines.append('nop/4')
        # Masked write
        lines.append('maskn 1')
        lines.append(f'fpassa $s15 $n{8*i + col_off}/1000')
        lines.append('nop/4')

with open('problems/16.onehot/solution.vsm', 'w') as f:
    f.write('\n'.join(lines) + '\n')
