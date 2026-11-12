#!/bin/sh
# usage: asmok.sh file.vsm -> prints OK or the assembler error
E=/home/wogikaze/wgkz/mncore/judge/judge-py/mncore2_emuenv
sed 's/[#!].*$//' "$1" | $E/assemble3 --instruction-mode flat > /tmp/asmok_out.txt 2>/tmp/asmok_err.txt && echo OK || (grep -v "^/\|^ *$\|^j \|^m " /tmp/asmok_err.txt | head -3)
