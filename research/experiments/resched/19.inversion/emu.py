import subprocess, re, struct
R='/home/wogikaze/wgkz/mncore/'
E=R+'judge/judge-py/mncore2_emuenv/'
tc=open(R+'problems/challenge/19.inversion/testcase.vsm').read()
M="# ======= YOUR VSM WILL BE INSERTED HERE ======="
PRE,SUF=tc.split(M)
def run(prog, dumps=None, suf=False):
    """prog: list of lines; dumps: {lineno(1-based, after): [getspec,...]}; returns list of (spec, raw lines)"""
    dumps=dumps or {}
    out=[]
    for s in dumps.get(0,[]): out.append('d '+s)
    for i,l in enumerate(prog,1):
        out.append(l)
        for s in dumps.get(i,[]): out.append('d '+s)
    vsm=PRE+'\n'.join(out)+'\n'+(SUF if suf else '')
    vsm=re.sub(r"[#!].*$","",vsm,flags=re.M)
    p=subprocess.run([E+'assemble3','--instruction-mode','flat'],input=vsm.encode(),capture_output=True)
    if p.returncode: return 'ASM:'+p.stderr.decode()
    asm='\n'.join(l for l in p.stdout.decode().split('\n') if l.split()[:1] in (['j'],['m'],[]) or l.startswith('d '))
    q=subprocess.run([E+'gpfn3_package_main'],input=asm.encode(),capture_output=True)
    return q.stderr.decode()
def vals(text):
    """parse to list of (tag, addr, hex64)"""
    r=[]
    for l in text.split('\n'):
        m=re.match(r'DEBUG-([A-Z0-9]+)\((\w+),(\d+)\):.*?v:0x([0-9A-Fa-f]+)',l)
        if m: r.append((m.group(2),int(m.group(3)),int(m.group(4),16)))
    return r
def f32(x): return struct.unpack('>f',struct.pack('>I',x))[0]
def pair(v): return (v>>32, v&0xffffffff)
