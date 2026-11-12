#!/bin/sh
# usage: tight.sh tc_tight.vsm cand.vsm -> per-position error vs expected (atol ~0)
T=$(realpath $1); F=$(realpath $2)
cd /home/wogikaze/wgkz/mncore/judge/judge-py && python3 judge.py $T $F 2>&1 | grep -E "MISMATCH|rror|ACCEPT" | sed 's/RESULT MISMATCH: //'
