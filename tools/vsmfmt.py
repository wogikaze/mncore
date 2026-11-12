#!/usr/bin/env python3
"""Column-align a VSM file by issue group.

    python3 tools/vsmfmt.py in.vsm [-o out.vsm] [--in-place] [--tabs N]

Each PE line is split at ';' into expressions, and every expression is put in the column of its issue group:

    ALU (imm, i*, f* scalar ops, l* long ops, nop) | MAU calc (?v*, ?m*) | MAU mwrite/mread | L1BM | L2BM | other

Only columns that are used somewhere in the file are emitted (L1BM and L2BM share a column when no line has
both). Inside a column the mnemonic is padded to the widest mnemonic of that column, so the operands line up too. Comment lines (#...), blank lines, MV lines and debug
lines (d ...) are passed through unchanged. Expressions are reordered into column order; the hardware issues at most
one expression per group per line, so the order inside a line has no meaning.
"""
import argparse, re, sys

COLS = ["alu", "mau", "mrw", "l1", "l2", "other"]

def group(expr):
    mn = expr.split()[0].split("/")[0].split("+")[0]
    if re.fullmatch(r"[dfhg]m(write|read)", mn): return "mrw"
    if re.fullmatch(r"[dfhg][vm](fma|mul|add|sub|passa)", mn): return "mau"
    if mn.startswith("l1bm"): return "l1"
    if mn.startswith("l2bm"): return "l2"
    if mn in ("noforward", "wait"): return "other"
    return "alu"

def is_code(line):
    s = line.strip()
    return bool(s) and not s.startswith("#") and not re.match(r"(mv\w*|d)\b", s.split()[0])

def split_mn(expr):
    parts = expr.split(None, 1)
    return parts[0], (parts[1].split() if len(parts) > 1 else [])

def fmt(lines, tabs=None):
    """tabs=None: pad with spaces ("a ; b").  tabs=N: pad with tab characters for a tab width of N ("a;<TAB>b"),
    every column (and the operands inside a column) starting on a tab stop."""
    rows = {}
    for i, l in enumerate(lines):
        if not is_code(l): continue
        r = {}
        for e in (x.strip() for x in l.split(";")):
            if not e: continue
            g = group(e)
            if g in r: raise SystemExit(f"line {i + 1}: two expressions of group {g}: {l!r}")
            r[g] = split_mn(e)
        rows[i] = r
    if not any("l1" in r and "l2" in r for r in rows.values()):    # share one column when they never co-issue
        for r in rows.values():
            if "l2" in r: r["l1"] = r.pop("l2")
    used = [c for c in COLS if any(c in r for r in rows.values())]
    present = lambda c: [r[c] for r in rows.values() if c in r]
    if tabs:
        N = tabs
        stop = lambda w: (w // N + 1) * N                      # next tab stop strictly after w characters
        def pad(s, target):                                    # tabs from len(s) up to the tab stop `target`
            pos, k = len(s.expandtabs(N)), 0
            while pos < target: pos = (pos // N + 1) * N; k += 1
            return s + "\t" * k
        mnw = {c: stop(max(len(mn) for mn, _ in present(c))) for c in used}
        def text(c, mo):
            mn, ops = mo
            return pad(mn, mnw[c]) + " ".join(ops) if ops else mn
        off, x = {}, 0
        for c in used:
            off[c] = x
            x = stop(x + max(len(text(c, mo).expandtabs(N)) for mo in present(c)) + 1)   # +1 for the ';'
        out = []
        for i, l in enumerate(lines):
            if i not in rows: out.append(l.rstrip("\n")); continue
            s = ""
            for c in used:
                if c not in rows[i]: continue
                if s: s += ";"
                s = pad(s, off[c]) + text(c, rows[i][c])
            out.append(s.rstrip())
        return out
    mnw = {c: max(len(mn) for mn, _ in present(c)) for c in used}
    def text(c, mo):
        mn, ops = mo
        return (mn.ljust(mnw[c]) + " " + " ".join(ops)).rstrip() if ops else mn
    off, x = {}, 0
    for c in used: off[c] = x; x += max(len(text(c, mo)) for mo in present(c)) + 3     # "<col> ; <col>"
    out = []
    for i, l in enumerate(lines):
        if i not in rows: out.append(l.rstrip("\n")); continue
        s = ""
        for c in used:
            if c not in rows[i]: continue
            t = text(c, rows[i][c])
            if s: s = s.ljust(off[c] - 2) + "; " + t
            else: s = " " * off[c] + t
        out.append(s.rstrip())
    return out

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("src"); ap.add_argument("-o"); ap.add_argument("--in-place", action="store_true")
    ap.add_argument("--tabs", type=int, metavar="N", help="align with tab characters for tab width N (e.g. 4)")
    a = ap.parse_args()
    res = "\n".join(fmt(open(a.src).read().splitlines(), a.tabs)) + "\n"
    dst = a.src if a.in_place else a.o
    if dst: open(dst, "w").write(res)
    else: sys.stdout.write(res)
