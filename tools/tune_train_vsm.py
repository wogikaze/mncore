#!/usr/bin/env python3

"""Hand tunings that the generator does not express yet.

Run after generating the training VSM and before ``tools/squeeze_nops.py``:

    python3 tools/tune_train_vsm.py viz/core/benchmarks/mnist_train_step.vsm

Currently it flips the Add -> Relu hand-off: the Relu reads the Add's LM1
output and writes LM0, the fc1 UL reads LM0, and the two DLs that used to
re-load fc1_pre and fc1 are removed.  The replica words are passed through
with fpassa so the register contents match what the DL used to load.
"""

import re
import sys


def blocks(lines):
    op_re = re.compile(r"^# --- Operation (\d+): (\S+) ---$")
    starts = [i for i, l in enumerate(lines) if op_re.match(l)]
    return [(s, starts[k + 1] if k + 1 < len(starts) else len(lines)) for k, s in enumerate(starts)]


def find(lines, name):
    for s, e in blocks(lines):
        if any(l.strip() == f"# Node name: {name}" for l in lines[s:e]):
            return s, e
    return None


def main(path):
    lines = open(path).read().splitlines()
    relu = find(lines, "fc1_relu")
    if relu is None:
        print("fc1_relu not found; nothing to do")
        return
    s, e = relu
    idx = [i for i in range(s, e) if lines[i].startswith("frelu")]
    if idx:
        new = [
            "frelu $n0v $n0v $m0v",
            "fpassa $n4v $m4v",
            "frelu $n8v $n8v $m8v",
            "fpassa $n12v $m12v",
        ]
        lines[s : e] = lines[s : idx[0]] + new + lines[idx[-1] + 1 : e]

    ul = find(lines, "fc1_UL")
    if ul:
        s, e = ul
        for i in range(s, e):
            if lines[i].startswith("l1bmm@0") and "$lln" in lines[i]:
                lines[i] = lines[i].replace("$lln", "$llm")

    for name in ("fc2_pre_gemm_DL_0", "fc1_relu_DL_0"):
        blk = find(lines, name)
        if blk:
            s, e = blk
            del lines[s:e]

    open(path, "w").write("\n".join(lines) + "\n")
    print(f"flipped the Add->Relu hand-off in {path}")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "viz/core/benchmarks/mnist_train_step.vsm")
