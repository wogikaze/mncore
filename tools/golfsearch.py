#!/usr/bin/env python3
"""Shorten a VSM answer by moving, merging and deleting whole expressions, checked by simulation.

    python3 tools/golfsearch.py <problem> [--start in.vsm] [--out best.vsm] [--minutes 10] [--window 6]
                                [--workers 10] [--seed 0]

The program is treated as lines of ';'-separated expressions; the expressions themselves are never edited.
Every candidate is run by `golfcheck.Checker` (native simulator, exact agreement with the recorded answer's
dumps). Two kinds of moves:

  shortening  delete a line; delete an expression; empty a line by moving each of its expressions into
              another line within --window lines (the line then disappears)
  plateau     swap two lines, move a line, or move one expression to another line, keeping the word count

Each round tries every shortening move (in parallel) and takes the first that passes. When none passes,
it takes a random walk of passing plateau moves and tries again, until --minutes run out. This finds what
rescheduling alone can save; it cannot change registers, constants or the algorithm. The result is only
a candidate: confirm it with problems/run_problem.py.
"""

from __future__ import annotations

import argparse
import random
import sys
import time
from multiprocessing import Pool
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

_checker = None


def _init(problem: str):
    global _checker
    from golfcheck import Checker

    _checker = Checker(problem)


def _test(lines):
    r = _checker.check(render(lines))
    return r.ok, r.words


def parse(text: str) -> list[list[str]]:
    out = []
    for raw in text.splitlines():
        line = raw.split("#")[0].strip()
        if not line:
            continue
        exprs = [e.strip() for e in line.split(";") if e.strip()]
        if exprs:
            out.append(exprs)
    return out


def render(lines) -> str:
    return "".join("; ".join(l) + "\n" for l in lines)


def is_mv(line) -> bool:
    return line[0].startswith("mv")


def movable(expr: str) -> bool:
    return not expr.startswith("mv")


def shortening_moves(lines, window):
    n = len(lines)
    for i in range(n):
        yield [l for k, l in enumerate(lines) if k != i]
    for i in range(n):
        if len(lines[i]) > 1:
            for e in range(len(lines[i])):
                yield [l if k != i else l[:e] + l[e + 1:] for k, l in enumerate(lines)]
    for i in range(n):
        if is_mv(lines[i]) or not all(movable(x) for x in lines[i]):
            continue
        targets = [j for j in range(max(0, i - window), min(n, i + window + 1)) if j != i and not is_mv(lines[j])]
        exprs = lines[i]
        if len(exprs) == 1:
            for j in targets:
                new = [list(l) for l in lines]
                new[j].append(exprs[0])
                del new[i]
                yield new
        else:
            # every expression into the same line, or each into its own nearest candidate
            for j in targets:
                new = [list(l) for l in lines]
                new[j].extend(exprs)
                del new[i]
                yield new
            for _ in range(len(targets) * 2):
                new = [list(l) for l in lines]
                for x in exprs:
                    new[random.choice(targets)].append(x)
                del new[i]
                yield new


def plateau_move(lines, window):
    n = len(lines)
    new = [list(l) for l in lines]
    kind = random.random()
    i = random.randrange(n)
    j = min(n - 1, max(0, i + random.randint(-window, window)))
    if i == j:
        return None
    if kind < 0.3:
        new[i], new[j] = new[j], new[i]
    elif kind < 0.5:
        new.insert(j, new.pop(i))
    else:
        if is_mv(new[i]) or is_mv(new[j]) or len(new[i]) < 2:
            return None
        e = random.randrange(len(new[i]))
        if not movable(new[i][e]):
            return None
        new[j].append(new[i].pop(e))
    return new


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("problem")
    ap.add_argument("--start")
    ap.add_argument("--out")
    ap.add_argument("--minutes", type=float, default=10)
    ap.add_argument("--window", type=int, default=6)
    ap.add_argument("--workers", type=int, default=10)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--walk", type=int, default=8, help="passing plateau moves per random walk")
    a = ap.parse_args(argv[1:])
    random.seed(a.seed)
    start = Path(a.start) if a.start else ROOT / "problems" / a.problem / "answer.vsm"
    out = Path(a.out or f"/tmp/golf-{a.problem.replace('/', '_')}.vsm")
    lines = parse(start.read_text(encoding="utf-8"))
    deadline = time.time() + a.minutes * 60
    with Pool(a.workers, initializer=_init, initargs=(a.problem,)) as pool:
        ok, words = pool.apply(_test, (lines,))
        if not ok:
            raise SystemExit("start program does not pass")
        best_words, best = words, lines
        print(f"start {words} words, {len(lines)} lines", flush=True)
        tried = 0
        while time.time() < deadline:
            cands = list(shortening_moves(lines, a.window))
            tried += len(cands)
            found = None
            for res, cand in zip(pool.imap(_test, cands, chunksize=4), cands):
                ok, w = res
                if ok and w < words:
                    found = (cand, w)
                    break
            if found:
                lines, words = found
                if words < best_words:
                    best_words, best = words, lines
                    out.write_text(render(best), encoding="utf-8")
                    print(f"{time.strftime('%H:%M:%S')} {words} words (tried {tried})", flush=True)
                continue
            # random walk on the plateau from the best program so far
            lines, steps = best, 0
            while steps < a.walk and time.time() < deadline:
                batch = [m for m in (plateau_move(lines, a.window) for _ in range(a.workers * 4)) if m]
                tried += len(batch)
                passing = [c for (ok, w), c in zip(pool.map(_test, batch), batch) if ok and w <= words]
                if passing:
                    lines = random.choice(passing)
                    steps += 1
    out.write_text(render(best), encoding="utf-8")
    print(f"best {best_words} words -> {out} (tried {tried})")


if __name__ == "__main__":
    main(sys.argv)
