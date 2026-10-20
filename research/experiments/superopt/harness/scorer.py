"""Scorer: in-process native simulator + official assembler pre-filter.

Two evaluation stages, both cached by program hash:

1. `assemble3` (official assembler, ~6 ms): rejects field conflicts, data
   races and unsupported forms.  A candidate that fails here can never be
   submitted, so paying 0.45 s of simulator time for it is waste.
2. `fbcheck.check` (native simulator against the official testcase, ~0.45 s):
   returns the mismatch count over all 4096 dumped long words.

The stage-1 filter is *sound*: `tools/fbverify.py` runs the same assembler
before the emulator, so an assembler error is a hard reject.  Every stage-2
result is exactly `tools/fbcheck.py`'s result.

The cache is a SQLite file shared by all campaigns.  Programs are stored
zlib-compressed so the best candidates can be recovered after the fact.
"""

from __future__ import annotations

import multiprocessing as mp
import os
import sqlite3
import sys
import time
import zlib
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]  # .../mncore
HERE = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))


# ------------------------------------------------------------------ worker side


def _init_worker() -> None:
    """Each worker gets its own native simulator process (spawn context).

    The native simulator links the `viz/core` engine, which uses a rayon pool.
    Each evaluation is a straight-line 93-step program, so extra threads only
    oversubscribe and spin; forcing one thread per simulator lets the worker
    pool scale linearly instead.
    """
    os.environ["RAYON_NUM_THREADS"] = "1"
    os.environ["OMP_NUM_THREADS"] = "1"
    import tools.fbcheck as fb

    fb.init()


def _assemble(text: str):
    """Official assembler without the unbounded in-process cache."""
    import mncompile.sim as ms

    asm = ms.assembler()
    result = asm.assemble(text)
    if len(asm.cache) > 4096:
        asm.cache.clear()
    return result


def _worker(task):
    key, text, do_asm, do_sim = task
    t0 = time.perf_counter()
    out = {"key": key, "stage": "?", "ok": 0, "words": 0, "lines": 0,
           "mismatches": None, "error": None, "asm_words": None}
    if do_asm:
        try:
            asm = _assemble(text)
        except Exception as exc:  # pragma: no cover - defensive
            out.update(stage="asm_error", error=f"assembler exception: {exc}")
            out["elapsed"] = time.perf_counter() - t0
            return out
        if not asm.ok:
            errs = (asm.error or "assembler failed").strip().splitlines()
            detail = ""
            for line in errs:
                s2 = line.strip()
                if (s2.startswith("what():") or "conflict" in s2.lower()
                        or ("error:" in s2.lower() and "terminate" not in s2.lower())):
                    detail = s2
                    break
            if not detail:
                detail = errs[0] if errs else "assembler failed"
            out.update(stage="asm_error", error=detail[:300])
            out["elapsed"] = time.perf_counter() - t0
            return out
        out["asm_words"] = asm.words
        out["words"] = asm.words
        if not do_sim:
            out["stage"] = "asm_ok"
            out["elapsed"] = time.perf_counter() - t0
            return out
    if do_sim:
        import tools.fbcheck as fb

        r = fb.check(text)
        out["lines"] = r.lines
        if out["words"] == 0:
            out["words"] = r.words or 0
        if r.error:
            out.update(stage="sim_error", error=r.error[:240], ok=0,
                       mismatches=None)
        else:
            out.update(stage="sim_ok" if r.ok else "sim_fail",
                       ok=1 if r.ok else 0, mismatches=r.mismatches)
    out["elapsed"] = time.perf_counter() - t0
    return out


# ------------------------------------------------------------------ results


@dataclass
class EvalResult:
    hash: str
    stage: str
    ok: bool
    words: int
    lines: int
    mismatches: int | None
    error: str | None
    asm_words: int | None
    family: str
    chain: str
    cached: bool = False

    @property
    def exact(self) -> bool:
        return self.stage in ("sim_ok", "sim_fail")

    def __str__(self):
        return (f"{self.stage} w={self.words} mis={self.mismatches} "
                f"err={self.error!r}")


SCHEMA = """
CREATE TABLE IF NOT EXISTS evals (
  hash TEXT PRIMARY KEY,
  text BLOB,
  stage TEXT,
  ok INTEGER,
  words INTEGER,
  lines INTEGER,
  mismatches INTEGER,
  error TEXT,
  asm_words INTEGER,
  elapsed REAL,
  ts REAL
);
CREATE INDEX IF NOT EXISTS evals_ok ON evals(ok, words, mismatches);
"""


class Scorer:
    def __init__(self, cache_path: str | Path | None = None, workers: int = 10,
                 asm_filter: bool = True, quiet: bool = False):
        self.cache_path = Path(cache_path or HERE / "cache" / "candidates.sqlite")
        self.cache_path.parent.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(str(self.cache_path))
        self.db.execute("PRAGMA journal_mode=WAL")
        self.db.execute("PRAGMA synchronous=NORMAL")
        self.db.executescript(SCHEMA)
        self.db.commit()
        self.workers = workers
        self.asm_filter = asm_filter
        self.quiet = quiet
        self.pool = None
        self.stats = {
            "submitted": 0, "cached": 0, "new": 0,
            "asm_error": 0, "asm_ok": 0, "sim_ok": 0, "sim_fail": 0,
            "sim_error": 0, "sim_seconds": 0.0, "asm_seconds": 0.0,
            "batch_seconds": 0.0,
        }

    # -- pool --
    def _ensure_pool(self):
        if self.pool is None and self.workers > 0:
            ctx = mp.get_context("spawn")
            self.pool = ctx.Pool(self.workers, initializer=_init_worker)
        return self.pool

    def close(self):
        if self.pool is not None:
            self.pool.close()
            self.pool.join()
            self.pool = None
        self.db.close()

    # -- cache --
    def get(self, h: str):
        cur = self.db.execute(
            "SELECT stage, ok, words, lines, mismatches, error, asm_words "
            "FROM evals WHERE hash=?", (h,))
        row = cur.fetchone()
        return row

    def _put(self, res: dict):
        text = res.get("text")
        blob = zlib.compress(text.encode()) if text else None
        self.db.execute(
            "INSERT OR REPLACE INTO evals(hash,text,stage,ok,words,lines,"
            "mismatches,error,asm_words,elapsed,ts) VALUES(?,?,?,?,?,?,?,?,?,?,?)",
            (res["key"], blob, res["stage"], res["ok"], res["words"],
             res.get("lines", 0), res["mismatches"], res["error"],
             res.get("asm_words"), res.get("elapsed", 0.0), time.time()))

    # -- main API --
    def evaluate(self, items: list[tuple[str, str, str]]) -> list[EvalResult]:
        """items: [(text, family, chain)]; returns results in input order."""
        t0 = time.perf_counter()
        import hashlib

        keys = [hashlib.sha256(t.encode()).hexdigest() for t, _, _ in items]
        results: list[EvalResult | None] = [None] * len(items)
        tasks = []
        task_idx = []
        for idx, (text, fam, chain) in enumerate(items):
            h = keys[idx]
            self.stats["submitted"] += 1
            row = self.get(h)
            if row is not None:
                self.stats["cached"] += 1
                stage, ok, words, lines, mis, err, asm_words = row
                results[idx] = EvalResult(h, stage, bool(ok), words, lines,
                                          mis, err, asm_words, fam, chain, cached=True)
                continue
            do_asm = self.asm_filter
            tasks.append((h, text, do_asm, True))
            task_idx.append(idx)
            self.stats["new"] += 1
        if tasks:
            outs = self._run(tasks)
            for idx, out in zip(task_idx, outs):
                out = dict(out)
                text = items[idx][0]
                out["text"] = text
                self._put(out)
                fam, chain = items[idx][1], items[idx][2]
                results[idx] = EvalResult(out["key"], out["stage"],
                                          bool(out["ok"]), out["words"],
                                          out.get("lines", 0),
                                          out["mismatches"], out["error"],
                                          out.get("asm_words"), fam, chain)
                st = out["stage"]
                if st in self.stats:
                    self.stats[st] += 1
                if st.startswith("sim"):
                    self.stats["sim_seconds"] += out.get("elapsed", 0.0)
                elif st.startswith("asm"):
                    self.stats["asm_seconds"] += out.get("elapsed", 0.0)
            self.db.commit()
        self.stats["batch_seconds"] += time.perf_counter() - t0
        return [r for r in results if r is not None]

    def _run(self, tasks):
        pool = self._ensure_pool()
        if pool is None:
            return [_worker(t) for t in tasks]
        return pool.map(_worker, tasks, chunksize=1)

    def throughput(self) -> dict:
        st = self.stats
        wall = st["batch_seconds"]
        sims = st["sim_ok"] + st["sim_fail"] + st["sim_error"]
        return {
            **st,
            "evaluated_new": st["new"],
            "simulated": sims,
            "wall_seconds": round(wall, 2),
            "new_per_second": round(st["new"] / wall, 2) if wall else None,
            "sim_per_second": round(sims / wall, 2) if wall else None,
        }

    # -- best-of queries --
    def best(self, limit: int = 20):
        cur = self.db.execute(
            "SELECT hash,stage,ok,words,lines,mismatches,error,text "
            "FROM evals WHERE ok=1 ORDER BY words ASC, hash LIMIT ?", (limit,))
        return cur.fetchall()
