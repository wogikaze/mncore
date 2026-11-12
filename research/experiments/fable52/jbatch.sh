#!/bin/sh
# usage: jbatch.sh <horizon> <timeout> <workers> "<opts A>" "<opts B>" ...   (runs the variants in parallel)
cd /home/wogikaze/wgkz/mncore-fizzbuzz/research/experiments/fable52
H=$1; T=$2; W=$3; shift 3
i=0
for v in "$@"; do
  i=$((i+1)); tag=$(echo "$v" | tr ' =' '__')
  ( python3 jopt.py $H $T workers=$W out=/tmp/jb_$tag.vsm $v > /tmp/jb_$tag.log 2>&1; echo "[$v] $(tail -2 /tmp/jb_$tag.log | tr '\n' ' ')" ) &
done
wait
