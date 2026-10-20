import sys, os
ROOT='/home/wogikaze/wgkz/mncore'
sys.path.insert(0,ROOT)
from mncompile.sim import simulator
_s=None
def run(prog, show=None, pe_filter=('n0c0b0m0p','n0c0b1m0p')):
    global _s
    if _s is None: _s=simulator()
    r=_s.run(prog)
    print('ERR' if r.error else 'OK', r.error, r.part, r.line, 'words',r.words)
    for (mem,pe,addr),v in sorted(r.dump.items()):
        if show and mem not in show: continue
        if not any(pe.startswith(p) for p in pe_filter): continue
        print(f'  {mem:8s} {pe:18s} {addr:4d} 0x{v:016x}')
    return r
if __name__=='__main__':
    run(sys.argv[1])
