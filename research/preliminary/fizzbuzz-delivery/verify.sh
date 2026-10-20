#!/usr/bin/env bash
# End-to-end verification of research/preliminary/fizzbuzz-delivery.
# Requires: python3, ortools (CP-SAT), the official assemble3/gpfn3 binaries
# already present under judge/judge-py/mncore2_emuenv/, and the repo tools.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
cd "$ROOT"
LOGD="$HERE/logs/verify"
mkdir -p "$LOGD"

echo "== 1. abstract delivery model: BFS + brute force + CP-SAT =="
python3 "$HERE/delivery_model.py" --check | tee "$LOGD/delivery_model.txt"
grep -q "BFS shortest delivery length: 8" "$LOGD/delivery_model.txt"
grep -q "CP-SAT K=7: INFEASIBLE" "$LOGD/delivery_model.txt"
grep -q "CP-SAT K=8: OPTIMAL" "$LOGD/delivery_model.txt"
grep -q "ALL CHECKS PASSED" "$LOGD/delivery_model.txt"

echo
echo "== 2. assembler probes: n limit and hazard gaps =="
python3 "$HERE/probe_isa.py" | tee "$LOGD/probe_isa.txt"
grep -q "OK   mvp PDM->DRAM n16384" "$LOGD/probe_isa.txt"
grep -q "FAIL mvp PDM->DRAM n32768" "$LOGD/probe_isa.txt"
grep -q "FAIL l1bmd, nop, l2bmd (1 nop)  \[must FAIL\]" "$LOGD/probe_isa.txt"
grep -q "OK   l1bmd, nop, nop, l2bmd (2 nop)  \[must OK\]" "$LOGD/probe_isa.txt"
grep -q "FAIL l2bmd, mvd/n512 (0 nop)  \[must FAIL\]" "$LOGD/probe_isa.txt"
grep -q "OK   l2bmd, nop, mvd/n512 (1 nop)  \[must OK\]" "$LOGD/probe_isa.txt"

echo
echo "== 3. max DRAM write per instruction word: mvp/n16384 writes 16384 words =="
python3 "$HERE/run_official.py" "$HERE/vsm/mvp16384.vsm" --init unique \
    --dump 0:1 --dump 8191:8192 --dump 16383:16384 | tee "$LOGD/mvp16384.txt"
grep -q "asm_words j=0 m=1" "$LOGD/mvp16384.txt"
grep -q "D16383 = 0x000000000007c001" "$LOGD/mvp16384.txt"

echo
echo "== 4. 9-word construction (one producer + the 8-word delivery) =="
python3 "$HERE/run_official.py" "$HERE/vsm/nine_word.vsm" --init zero \
    --dump 0:1 --dump 2047:2048 --dump 4095:4096 | tee "$LOGD/nine_word.txt"
grep -q "asm_words j=7 m=2" "$LOGD/nine_word.txt"
grep -q "D0 = 0x1234567812345678" "$LOGD/nine_word.txt"
grep -q "D4095 = 0x1234567812345678" "$LOGD/nine_word.txt"

echo
echo "== 5. capacity of one l2bmd: deleting one of the two gives 2048 mismatches =="
python3 tools/fbcheck.py "$HERE/vsm/one_l2bmd.vsm" | tee "$LOGD/one_l2bmd.txt" || true
grep -q "mismatches=2048" "$LOGD/one_l2bmd.txt"

echo
echo "== 6. \$-aluf shortcut: 92 words but 4096 mismatches (negative result) =="
python3 tools/fbcheck.py "$HERE/vsm/aluf_92.vsm" | tee "$LOGD/aluf_92.txt" || true
grep -q "mismatches=4096" "$LOGD/aluf_92.txt"

echo
echo "== 7. delivery tail of the accepted solution: 8 words =="
./judge/judge-py/mncore2_emuenv/assemble3 --instruction-mode flat \
    "$HERE/vsm/delivery_tail.vsm" > "$LOGD/delivery_tail.asm" 2> "$LOGD/delivery_tail.err"
test "$(grep -c '^j ' "$LOGD/delivery_tail.asm")" = 6
test "$(grep -c '^m ' "$LOGD/delivery_tail.asm")" = 2
echo "delivery tail: j=6 m=2 => 8 assembled words"

echo
echo "== 8. official gate on the accepted 93-word solution =="
python3 tools/fbverify.py problems/challenge/20.fizzbuzz/answer.vsm | tee "$LOGD/fbverify_answer.txt"
grep -q "ACCEPTED!! score=93 j=91 m=2" "$LOGD/fbverify_answer.txt"

echo
echo "ALL VERIFICATION STEPS PASSED"
