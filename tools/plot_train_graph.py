#!/usr/bin/env python3

"""Render the MNIST train-step computation graph as SVG.

The graph is recovered from the generated VSM: a compute operator's input is
traced back through its DL -> DRAM tensor -> UL chain to the operator that
produced it.  DL/UL transfers and the output aliases are omitted; the number in
each box is that operator's own instruction lines in the VSM.

    python3 tools/plot_train_graph.py [vsm] [out.svg]
"""

import re
import sys
from typing import Dict, List, Set, Tuple

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams["font.family"] = ["Noto Sans CJK JP", "DejaVu Sans"]
plt.rcParams["svg.fonttype"] = "path"
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch

SRC = sys.argv[1] if len(sys.argv) > 1 else "viz/core/benchmarks/mnist_train_step.vsm"
OUT = sys.argv[2] if len(sys.argv) > 2 else "docs/mnist-train-step-graph.svg"

HEADER = re.compile(r"# --- Operation (\d+): (\S+) ---")
TENSOR = re.compile(
    r"# (Input\d+|Output\d+): (\S+), shape=(.*?), (?:type=\S+, )?addr=(\d+), "
    r"layout=(.*), len=(\d+), location=(\S+)"
)


def parse(path: str):
    ops = []
    cur = None
    for line in open(path):
        m = HEADER.match(line)
        if m:
            cur = {"n": int(m.group(1)), "type": m.group(2), "name": None,
                   "in": [], "out": [], "size": 0}
            ops.append(cur)
            continue
        if cur is None:
            continue
        m = re.match(r"# Node name: (\S+)", line)
        if m:
            cur["name"] = m.group(1)
        m = TENSOR.match(line)
        if m:
            d = {"t": m.group(2), "shape": m.group(3)}
            (cur["in"] if m.group(1).startswith("Input") else cur["out"]).append(d)
        if line.split("#")[0].strip():
            cur["size"] += 1
    return ops


def build_graph(ops):
    out_map = {}
    for o in ops:
        for d in o["out"]:
            out_map[d["t"]] = o

    graph_inputs: Set[str] = set()
    for o in ops:
        if o["type"] == "DL" and o["in"] and o["in"][0]["t"] not in out_map:
            graph_inputs.add(o["in"][0]["t"])

    def resolve(t, seen=None):
        seen = seen or set()
        if t in seen:
            return None
        seen.add(t)
        if t in graph_inputs:
            return ("in", t)
        o = out_map.get(t)
        if o is None:
            return None
        if o["type"] in ("DL", "UL", "Identity"):
            return resolve(o["in"][0]["t"], seen) if o["in"] else None
        return ("op", o["n"])

    edges = set()
    for o in ops:
        if o["type"] in ("DL", "UL", "Identity"):
            continue
        for d in o["in"]:
            r = resolve(d["t"])
            if r:
                edges.add((f"in:{r[1]}" if r[0] == "in" else f"op:{r[1]}", f"op:{o['n']}"))

    text = open(SRC).read()
    op_outputs: Dict[int, List[str]] = {}
    for m in re.finditer(
        r"# --- Operation \d+: Identity ---\n# Node name: \S+\n(?:# Attr:.*\n)*"
        r"# Input0: (\S+),.*\n# Output0: (\S+),",
        text,
    ):
        r = resolve(m.group(1))
        if r and r[0] == "op":
            op_outputs.setdefault(r[1], []).append(m.group(2))

    nodes = set()
    for a, b in edges:
        nodes.add(a)
        nodes.add(b)
    for o in ops:
        if o["type"] not in ("DL", "UL", "Identity"):
            nodes.add(f"op:{o['n']}")
    return nodes, edges, {o["n"]: o for o in ops}, op_outputs


# ---- layout -----------------------------------------------------------------

def layers_of(nodes, edges):
    preds: Dict[str, List[str]] = {n: [] for n in nodes}
    for a, b in edges:
        preds[b].append(a)
    layer: Dict[str, int] = {}
    order = []
    remaining = set(nodes)
    while remaining:
        ready = [n for n in remaining if all(p in layer for p in preds[n])]
        for n in ready:
            layer[n] = 0 if not preds[n] else max(layer[p] + 1 for p in preds[n])
            order.append(n)
            remaining.remove(n)
    return layer


STYLE = {
    "Gemm": ("#dbe7f5", "#2f5d8a"),
    "Add": ("#dbe7f5", "#2f5d8a"),
    "Relu": ("#dbe7f5", "#2f5d8a"),
    "ReduceMax": ("#dcefe1", "#2f7a52"),
    "Sub": ("#dcefe1", "#2f7a52"),
    "Exp": ("#dcefe1", "#2f7a52"),
    "ReduceSum": ("#dcefe1", "#2f7a52"),
    "Div": ("#dcefe1", "#2f7a52"),
    "OneHot": ("#dcefe1", "#2f7a52"),
    "LossGrad": ("#fbe3d0", "#a85a1c"),
    "ReluGrad": ("#fbe3d0", "#a85a1c"),
    "SGDUpdate": ("#e7dcf4", "#5f4390"),
    "in": ("#ececec", "#666666"),
    "out": ("#fff3c9", "#8a6d0b"),
}

PHASES = [
    (0, 5, "forward (fc1 → relu → fc2)", "#f4f8fd"),
    (6, 11, "softmax + loss", "#f2faf5"),
    (12, 15, "backward", "#fdf6ef"),
    (16, 16, "optimizer", "#f8f4fd"),
]


PRETTY = {
    "fc1_pre_gemm": "fc1 pre-activation",
    "fc1_pre_add_bias": "fc1 + bias",
    "fc1_relu": "relu",
    "fc2_pre_gemm": "fc2 pre-activation",
    "fc2_pre_add_bias": "fc2 + bias",
    "_reducemax": "row max",
    "_sub": "x - max",
    "_exp": "exp",
    "_reducesum": "row sum",
    "_div": "exp / sum",
    "OneHot_11": "target one-hot",
    "LossGrad_12": "(probs - target) x s",
    "grad_fc2_weight_gemm": "grad fc2 weight",
    "ReduceSum_14": "bias grad fc2",
    "Gemm_15": "grad fc2 input",
    "ReluGrad_16": "grad x (x > 0)",
    "grad_fc1_weight_gemm": "grad fc1 weight",
    "ReduceSum_20": "bias grad fc1",
}


def short_name(name: str, kind: str) -> str:
    if name is None:
        return ""
    name = re.sub(r"_(DL|UL)_\d+(_out)?$", "", name)
    name = name.replace("_UL_out", "")
    if name in PRETTY:
        return PRETTY[name]
    return name


def main():
    ops = parse(SRC)
    nodes, edges, by_n, op_outputs = build_graph(ops)
    layer = layers_of(nodes, edges)

    # order within each layer: barycenter of predecessors, inputs in declaration order
    layers: Dict[int, List[str]] = {}
    for n in nodes:
        layers.setdefault(layer[n], []).append(n)
    for L in layers:
        layers[L].sort()

    pos: Dict[str, Tuple[float, float]] = {}
    y_of = lambda L: -L * 0.92
    for L in sorted(layers):
        ns = layers[L]
        if L == 0:
            # inputs: fixed order, centred
            order = ["in:input", "in:fc1_weight", "in:fc1_bias",
                     "in:fc2_weight", "in:fc2_bias", "in:target"]
            ns = [n for n in order if n in ns] + [n for n in ns if n not in order]
        else:
            def bary(n):
                ps = [pos[p][0] for (a, b) in edges if b == n and (p := a) in pos]
                return sum(ps) / len(ps) if ps else 0.0
            for _ in range(2):
                ns.sort(key=bary)
        width = (len(ns) - 1) * 1.55
        for i, n in enumerate(ns):
            pos[n] = (-width / 2 + i * 1.55, y_of(L))

    xs = [p[0] for p in pos.values()]
    ys = [p[1] for p in pos.values()]
    x0, x1 = min(xs) - 1.3, max(xs) + 1.3
    y0, y1 = min(ys) - 0.9, max(ys) + 0.9

    fig_w = (x1 - x0) * 1.05
    fig_h = (y1 - y0) * 1.05
    fig, ax = plt.subplots(figsize=(fig_w, fig_h), dpi=110)
    ax.set_xlim(x0, x1)
    ax.set_ylim(y0, y1)
    ax.axis("off")

    # legend
    items = [("forward", STYLE["Gemm"]), ("softmax", STYLE["Exp"]),
             ("loss / backward", STYLE["LossGrad"]), ("optimizer", STYLE["SGDUpdate"])]
    lx = x0 + 0.1
    for label, (fill, edge) in items:
        ax.add_patch(FancyBboxPatch((lx, y0 + 0.12), 0.28, 0.2,
                                    boxstyle="round,pad=0.01,rounding_size=0.04",
                                    facecolor=fill, edgecolor=edge, lw=0.8, zorder=2))
        ax.text(lx + 0.36, y0 + 0.22, label, fontsize=6.6, va="center", color="#555555")
        lx += 0.36 + len(label) * 0.075 + 0.45

    # edges behind the boxes
    sgd_params = {}
    for a, b in edges:
        if a.startswith("in:") and b.startswith("op:"):
            o = by_n[int(b.split(":")[1])]
            if o["type"] == "SGDUpdate":
                sgd_params[b] = a.split(":", 1)[1]
    for a, b in edges:
        if a not in pos or b not in pos:
            continue
        if b in sgd_params and a == "in:" + sgd_params[b]:
            continue
        xa, ya = pos[a]
        xb, yb = pos[b]
        span = abs(layer[b] - layer[a])
        if span > 2:
            rad = (0.26 if xb >= xa else -0.26) * min(1.0, 0.55 + 0.09 * span)
            ax.add_patch(FancyArrowPatch(
                (xa, ya - 0.28), (xb, yb + 0.28),
                connectionstyle=f"arc3,rad={rad:.3f}", arrowstyle="-|>",
                mutation_scale=7, lw=0.7, color="#a7b0b8", zorder=1,
                shrinkA=0, shrinkB=0))
        else:
            ax.add_patch(FancyArrowPatch(
                (xa, ya - 0.28), (xb, yb + 0.28),
                connectionstyle="arc3,rad=0.0", arrowstyle="-|>",
                mutation_scale=7, lw=0.8, color="#8d979f", zorder=1,
                shrinkA=0, shrinkB=0))

    # nodes
    for n, (x, y) in pos.items():
        kind = n.split(":", 1)[0]
        if kind == "out":
            fill, edge = STYLE["out"]
            label1 = "output"
            label2 = n.split(":", 1)[1]
            label3 = ""
            weight = "bold"
        elif kind == "in":
            fill, edge = STYLE["in"]
            label1 = n.split(":", 1)[1]
            label2 = ""
            label3 = ""
            weight = "normal"
        else:
            num = int(n.split(":", 1)[1])
            o = by_n[num]
            fill, edge = STYLE.get(o["type"], ("#eeeeee", "#999999"))
            label1 = o["type"]
            label2 = short_name(o["name"], o["type"])[:22]
            label3 = f'{o["size"]} 行'
            key = f"op:{num}"
            if key in sgd_params:
                label2 = "in-place " + sgd_params[key].replace("_", " ")
            outs = op_outputs.get(num, [])
            if outs:
                label3 += "  → " + ", ".join(outs)[:26]
            weight = "bold"

        w, h = 1.72, 0.66
        ax.add_patch(FancyBboxPatch(
            (x - w / 2, y - h / 2), w, h,
            boxstyle="round,pad=0.02,rounding_size=0.08",
            facecolor=fill, edgecolor=edge, lw=0.9, zorder=2))
        ax.text(x, y + 0.165, label1, fontsize=8.4, ha="center", va="center",
                fontweight=weight, color="#222222", zorder=3)
        if label2:
            ax.text(x, y - 0.005, label2, fontsize=6.8, ha="center", va="center",
                    color="#333333", zorder=3)
        if label3:
            ax.text(x, y - 0.175, label3, fontsize=6.4, ha="center", va="center",
                    color="#777777", zorder=3)

    ax.text(0.0, y_of(0) + 1.02, "MNIST train step — compute graph (from the generated VSM)",
            ha="left", va="bottom", fontsize=11, fontweight="bold")
    raw_lines = len(open(SRC).read().splitlines())
    instr_lines = sum(1 for l in open(SRC) if l.split("#")[0].strip())
    compute = sum(o["size"] for o in by_n.values() if o["type"] not in ("DL", "UL", "Identity"))
    n_dl = sum(1 for o in by_n.values() if o["type"] == "DL")
    n_ul = sum(1 for o in by_n.values() if o["type"] == "UL")
    ax.text(0.0, y_of(0) + 0.72,
            f"{raw_lines:,} source lines / {instr_lines:,} instruction lines. The compute operators above are "
            f"{compute} lines; the other {instr_lines - compute:,} are {n_dl} DL / {n_ul} UL transfers and nops.",
            ha="left", va="bottom", fontsize=6.8, color="#666666")

    fig.savefig(OUT, format="svg", bbox_inches="tight", pad_inches=0.08)
    fig.savefig(OUT.replace(".svg", ".png"), dpi=150, bbox_inches="tight", pad_inches=0.08)
    fig.savefig("scratch/mnist-graph-preview.png", dpi=110, bbox_inches="tight", pad_inches=0.08)
    print("wrote", OUT)


if __name__ == "__main__":
    main()
