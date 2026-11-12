#!/bin/sh
# usage: emu.sh file.vsm  -> assemble (flat) + emulate, print debug output (d get lines kept)
E=/home/wogikaze/wgkz/mncore/judge/judge-py/mncore2_emuenv
sed 's/[#!].*$//' "$1" | $E/assemble3 --instruction-mode flat > /tmp/cu_asm.txt || exit 1
OMP_THREAD_LIMIT=1 $E/gpfn3_package_main --offchip-memory-init zero < /tmp/cu_asm.txt 2>&1
