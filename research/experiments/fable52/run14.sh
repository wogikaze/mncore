#!/bin/sh
# usage: run14.sh <tag> <start_cfg.json> [iters]
cd /home/wogikaze/wgkz/mncore-fizzbuzz/research/experiments/fable52
tag=$1; start=$2; iters=${3:-5000}
python3 search14.py $iters 12 $start > /tmp/search14_$tag.log 2>&1
tail -2 /tmp/search14_$tag.log
cp /tmp/cfg14_best.json /tmp/cfg14_best_$tag.json; cp /tmp/v14s.vsm /tmp/v14s_$tag.vsm
python3 exsa.py gen14 search14 /tmp/cfg14_best_$tag.json 200 12 8 > /tmp/exsa14_$tag.log 2>&1
tail -2 /tmp/exsa14_$tag.log
cp /tmp/exsa_best.json /tmp/exsa14_$tag.json; cp /tmp/exsa.vsm /tmp/exsa14_$tag.vsm
