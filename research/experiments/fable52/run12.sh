#!/bin/sh
# usage: run12.sh <iters> <tag:opts>...   e.g. run12.sh 5000 A:o_mtab=1 B:o_mtab=1,o_xd=1,o_dyd=1
cd /home/wogikaze/wgkz/mncore-fizzbuzz/research/experiments/fable52
iters=$1; shift
for spec in "$@"; do
tag=${spec%%:*}; opts=${spec#*:}
python3 - "$tag" "$opts" <<'PY'
import sys, json, random, gen12, search12
tag, opts = sys.argv[1], sys.argv[2]
start = dict(gen12.DEFAULT)
for k, v in json.load(open("cfg9_55.json")).items():
    if k in start: start[k] = v
start.update(o_ubf=0)
for kv in opts.split(","):
    k, v = kv.split("="); start[k] = int(v)
r = search12.repair(start, random.Random(7), gen=gen12)
json.dump(r, open(f"/tmp/cfg12_s{tag}.json", "w"), indent=0, sort_keys=True)
print(tag, "start lines", search12.evaluate(r, 50)[0])
PY
python3 search12.py $iters 12 /tmp/cfg12_s$tag.json > /tmp/search12_$tag.log 2>&1
cp /tmp/cfg12_best.json /tmp/cfg12_best_$tag.json; cp /tmp/v12s.vsm /tmp/v12s_$tag.vsm
echo "$tag $opts"; tail -2 /tmp/search12_$tag.log
done
