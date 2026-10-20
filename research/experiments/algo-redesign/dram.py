"""Run a VSM snippet on the native simulator and return the 4096 DRAM words."""
import sys, re, codecs
ROOT='/home/wogikaze/wgkz/mncore'
sys.path.insert(0,ROOT)
from mncompile.sim import simulator
_s=None
SUF='\n'.join(f'd getd $d{i}n0 1' for i in range(4096))+'\n'
def run(prog, suf=SUF):
    global _s
    if _s is None: _s=simulator()
    r=_s.run(prog, suffix=suf)
    if r.error:
        raise SystemExit(f'ERROR {r.part}:{r.line}: {r.error}')
    words={}
    for (mem,pe,addr),v in r.dump.items():
        if mem=='DRAM': words[addr]=v
    return [words.get(i,0) for i in range(4096)], r.words
def expected():
    out={}
    tc=open(ROOT+'/problems/challenge/20.fizzbuzz/testcase.vsm').read()
    for m in re.finditer(r'd getd \$d(\d+)n0 1\s*#\s*expect="([^"]*)"',tc):
        out[int(m.group(1))]=codecs.decode(m.group(2),'unicode_escape').encode('latin-1')
    return out
def report(prog):
    ws,words_count=run(prog)
    exp=expected(); mism=0
    for i in range(4096):
        e=exp[i]; got=ws[i].to_bytes(8,'big')
        if got[:len(e)]!=e:
            mism+=1
            if mism<=5: print('mismatch',i,got,e)
    print('words',words_count,'mismatches',mism)
    return ws
if __name__=='__main__':
    import pathlib
    report(pathlib.Path(sys.argv[1]).read_text())
