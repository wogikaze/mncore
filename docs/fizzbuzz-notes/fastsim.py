#!/usr/bin/env python3
"""Fast candidate checker: native simulator + expected DRAM comparison.

Usage (import):
    import fastsim
    fastsim.init()                      # loads testcase prefix/suffix, expectations
    res = fastsim.check(text, verify=True)
    res.ok, res.error, res.words, res.mismatches, res.lines, res.score
"""
import codecs
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
TESTCASE = os.path.join(ROOT, "problems", "challenge", "20.fizzbuzz", "testcase.vsm")
MARKER = "# ======= YOUR VSM WILL BE INSERTED HERE ======="

_sim = None
_expected = None
_pre = _suf = None


class Result:
    def __init__(self, ok, error, words, mismatches, lines, score, detail=""):
        self.ok = ok
        self.error = error
        self.words = words
        self.mismatches = mismatches
        self.lines = lines
        self.score = score
        self.detail = detail

    def __repr__(self):
        return (f"Result(ok={self.ok}, score={self.score}, lines={self.lines}, "
                f"words={self.words}, err={self.error!r}, mism={self.mismatches})")


def init():
    global _sim, _expected, _pre, _suf
    if _sim is not None:
        return
    sys.path.insert(0, ROOT)
    from mncompile.sim import simulator
    tc = open(TESTCASE).read()
    _pre, _suf = tc.split(MARKER, 1)
    _expected = {}
    for m in re.finditer(r'd getd \$d(\d+)n0 1\s*#\s*expect="([^"]*)"', tc):
        _expected[int(m.group(1))] = codecs.decode(m.group(2), "unicode_escape").encode("latin-1")
    _sim = simulator()
    _sim.register("fb_pre", _pre)
    _sim.register("fb_suf", _suf)
    _sim.register_expect("fb", [(0, addr, e) for addr, e in sorted(_expected.items())])


def score_of(text):
    pe_lines = 0
    mv_lines = 0
    for raw in text.split("\n"):
        line = raw.split("#")[0].strip()
        if not line:
            continue
        parts = [p for p in line.split(";")]
        has_pe = any(not re.match(r"\s*mv[a-z]*[/ ]", p) for p in parts)
        if has_pe:
            pe_lines += 1
        else:
            mv_lines += 1
    return pe_lines + mv_lines, pe_lines, mv_lines


def check(text, verify=True):
    """Fast path: run with the direct DRAM comparison (no d get lines)."""
    init()
    lines, pe, mv = score_of(text)
    r = _sim.run_expect(text, "fb")
    if r.error:
        return Result(False, f"{r.part}:{r.line}: {r.error}", r.words, None, lines, lines)
    mism = r.mism
    ok = (mism == 0) if verify else True
    return Result(ok, None, r.words, mism, lines, lines,
                  detail="" if ok else f"{mism} mismatches")


def batch(texts, threads=8):
    init()
    rs = _sim.batch_expect(texts, "fb", threads=threads)
    out = []
    for text, r in zip(texts, rs):
        lines, pe, mv = score_of(text)
        if r.error:
            out.append(Result(False, f"{r.part}:{r.line}: {r.error}", r.words, None, lines, lines))
        else:
            ok = r.mism == 0
            out.append(Result(ok, None, r.words, r.mism, lines, lines,
                              detail="" if ok else f"{r.mism} mismatches"))
    return out


def check_full(text, verify=True):
    """Reference path: the real testcase prefix/suffix harness with d getd lines."""
    init()
    lines, pe, mv = score_of(text)
    r = _sim.run(text, prefix_key="fb_pre", suffix_key="fb_suf")
    if r.error:
        return Result(False, f"{r.part}:{r.line}: {r.error}", r.words, None, lines, lines)
    mism = None
    if verify:
        mism = 0
        for (mem, peid, addr), val in r.dump.items():
            if mem != "DRAM":
                continue
            e = _expected.get(addr)
            if e is None:
                continue
            b = val.to_bytes(8, "big")
            n = min(len(e), 8)
            if b[:n] != e[:n]:
                mism += 1
    ok = mism == 0
    return Result(ok, None, r.words, mism, lines, lines,
                  detail="" if ok else f"{mism} mismatches")


if __name__ == "__main__":
    import time
    init()
    sol = open(sys.argv[1] if len(sys.argv) > 1 else
               os.path.join(ROOT, "problems", "challenge", "20.fizzbuzz", "main.vsm")).read()
    t0 = time.time()
    res = check(sol)
    print(f"{time.time()-t0:.3f}s {res}")
