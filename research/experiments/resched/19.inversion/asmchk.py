import subprocess,sys,re
E='/home/wogikaze/wgkz/mncore/judge/judge-py/mncore2_emuenv/'
def asm(lines):
    p=subprocess.run([E+'assemble3','--instruction-mode','flat'],input=('\n'.join(lines)+'\n').encode(),capture_output=True)
    return p.returncode==0, p.stderr.decode().split('\n')[0][:200]
if __name__=='__main__':
    print(asm(open(sys.argv[1]).read().split('\n')))
