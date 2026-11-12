#!/bin/sh
# usage: run10.sh <iters> ; runs the gen10 search for the four (o_xd, o_dyd) combinations
cd /home/wogikaze/wgkz/mncore-fizzbuzz/research/experiments/fable52
for tag in 00 01 10 11; do
python3 - "$tag" <<'PY'
import sys, json, random, gen10, search10
tag = sys.argv[1]
start = dict(gen10.DEFAULT)
for k, v in json.load(open("cfg9_55.json")).items():
    if k in start: start[k] = v
start.update(o_xd=int(tag[0]), o_dyd=int(tag[1]))
r = search10.repair(start, random.Random(7), gen=gen10)
json.dump(r, open(f"/tmp/cfg10_s{tag}.json", "w"), indent=0, sort_keys=True)
PY
python3 search10.py $1 12 /tmp/cfg10_s$tag.json > /tmp/search10_$tag.log 2>&1
cp /tmp/cfg10_best.json /tmp/cfg10_best_$tag.json; cp /tmp/v10s.vsm /tmp/v10s_$tag.vsm
tail -2 /tmp/search10_$tag.log
done
