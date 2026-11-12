#!/usr/bin/env python3
"""Add /1000 write masks to imm destinations that are fixed addresses (no v, not $t, no existing mask)."""
import re, sys
def fix_line(line):
    exprs = [e.strip() for e in line.split(';')]
    out = []
    for e in exprs:
        if e.startswith('imm'):
            toks = e.split()
            new = toks[:2]
            for d in toks[2:]:
                if '/' in d or d in ('$t', '$lt', '$llt') or re.search(r'v\d*$', d):
                    new.append(d)
                else:
                    new.append(d + '/1000')
            e = ' '.join(new)
        out.append(e)
    return '; '.join(out)
if __name__ == "__main__":
    src = open(sys.argv[1]).read().splitlines()
    open(sys.argv[2], 'w').write('\n'.join(fix_line(l) for l in src) + '\n')
