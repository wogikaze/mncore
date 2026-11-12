#!/bin/sh
cd /home/wogikaze/wgkz/mncore-fizzbuzz/research/experiments/fable52
python3 - <<'PY'
import json, random, gen13, search13
c = json.load(open("cfg13_54.json")); c.update(o_mtab=1, o_tabalu=0)
r = search13.repair(c, random.Random(5), gen=gen13)
json.dump(r, open("/tmp/cfg13_mt_start.json", "w"), indent=0, sort_keys=True)
print("start", search13.evaluate(r, 50, gen=gen13)[0])
PY
python3 search13.py 5000 12 /tmp/cfg13_mt_start.json > /tmp/search13_mt.log 2>&1
tail -2 /tmp/search13_mt.log
cp /tmp/cfg13_best.json /tmp/cfg13_best_mt.json; cp /tmp/v13s.vsm /tmp/v13s_mt.vsm
python3 exsa.py gen13 search13 /tmp/cfg13_best_mt.json 200 12 8 > /tmp/exsa13_mt.log 2>&1
tail -2 /tmp/exsa13_mt.log
cp /tmp/exsa_best.json /tmp/exsa13_mt.json; cp /tmp/exsa.vsm /tmp/exsa13_mt.vsm
