#!/usr/bin/env python3
"""Search campaign over the 93-word FizzBuzz baseline.

Waves
-----
seed      baseline, and the official-assembler cross-check
singles   one-step neighbourhood: delete/repair/merge/split/reorder/swap/
          relocate/commute/const/addr/noforward
moves     move one expression to every other row (the packing neighbourhood)
dissolve  move both expressions of a 2-expression row into two other rows
probe     a random sample of moves evaluated *without* the assembler filter,
          to record the simulator mismatch distribution for candidates the
          assembler rejects (failure-mode evidence)
anneal    simulated annealing / beam over the same transformations, starting
          from the best word-neutral states found by the waves above

Everything is cached in SQLite by program hash, so reruns are free and the
campaign can be interrupted and resumed.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(HERE))

from harness import scorer, transforms, vsmx  # noqa: E402

BASELINE = ROOT / "problems/challenge/20.fizzbuzz/answer.vsm"
BEST = HERE / "best"
LOGS = HERE / "logs"
CACHE = HERE / "cache" / "candidates.sqlite"


class Campaign:
    def __init__(self, workers: int, asm_filter: bool = True, tag: str = "main"):
        self.base_text = BASELINE.read_text()
        self.base = vsmx.parse(self.base_text)
        self.sc = scorer.Scorer(CACHE, workers=workers, asm_filter=asm_filter,
                                quiet=True)
        self.tag = tag
        self.best_words = 93
        self.best = None
        self.seen = set()
        self.results: list = []
        self.family_stats = defaultdict(Counter)
        self.mismatch_hist = Counter()
        self.error_hist = Counter()
        self.wave_stats = {}
        self.log_path = LOGS / f"campaign-{tag}.log"
        LOGS.mkdir(exist_ok=True, parents=True)
        BEST.mkdir(exist_ok=True, parents=True)
        self.log_file = open(self.log_path, "a", buffering=1)
        self.t_start = time.time()
        self.n_submitted = 0

    def log(self, msg: str):
        line = f"[{time.strftime('%H:%M:%S')}] {msg}"
        print(line, flush=True)
        self.log_file.write(line + "\n")

    # ------------------------------------------------------------------ utils
    def _items(self, mutations):
        out = []
        for m in mutations:
            text = m.program.text()
            out.append((text, m.family, " | ".join(m.program.chain[-3:])))
        return out

    def run_wave(self, name: str, mutations, limit: int | None = None,
                 batch: int = 400, asm_filter: bool | None = None):
        """Stream a mutation generator through the scorer in batches."""
        t0 = time.time()
        self.sc.asm_filter = True if asm_filter is None else asm_filter
        before = dict(self.sc.stats)
        n = 0
        chunk = []
        chunk_meta = []
        for m in mutations:
            if limit is not None and n + len(chunk) >= limit:
                break
            chunk.append(m.program.text())
            chunk_meta.append((m.family, " | ".join(m.program.chain[-3:])))
            if len(chunk) < batch:
                continue
            n += len(chunk)
            self._run_chunk(name, chunk, chunk_meta, n)
            chunk, chunk_meta = [], []
            if (n // batch) % 5 == 0:
                self.log(f"  {name}: {n} best={self.best_words}")
        if chunk:
            n += len(chunk)
            self._run_chunk(name, chunk, chunk_meta, n)
        st = self.sc.throughput()
        delta = {k: st[k] - before.get(k, 0) for k in
                 ("new", "cached", "asm_error", "sim_ok", "sim_fail",
                  "sim_error", "batch_seconds")}
        wall = delta["batch_seconds"]
        ws = {
            "wave": name, "items": n, "new": delta["new"],
            "cached": delta["cached"], "asm_error": delta["asm_error"],
            "sim_ok": delta["sim_ok"], "sim_fail": delta["sim_fail"],
            "sim_error": delta["sim_error"],
            "simulated": delta["sim_ok"] + delta["sim_fail"] + delta["sim_error"],
            "wall_s": round(wall, 1),
            "new_per_s": round(delta["new"] / wall, 2) if wall else None,
            "best_words": self.best_words,
        }
        self.wave_stats[name] = ws
        self.log(f"wave {name}: {json.dumps(ws)}")
        self.log_file.write(json.dumps({"wave": ws,
                                        "family_stats": self._family_json()}) + "\n")
        return ws

    def _run_chunk(self, name, texts, meta, n):
        items = [(t, f, ch) for t, (f, ch) in zip(texts, meta)]
        rs = self.sc.evaluate(items)
        self.results.extend(rs)
        self.n_submitted += len(items)
        self._observe(rs)

    def _observe(self, rs):
        for r in rs:
            key = r.family or "?"
            self.family_stats[key][r.stage] += 1
            if r.mismatches is not None:
                if r.mismatches == 0:
                    self.mismatch_hist["0"] += 1
                elif r.mismatches < 10:
                    self.mismatch_hist["1-9"] += 1
                elif r.mismatches < 100:
                    self.mismatch_hist["10-99"] += 1
                elif r.mismatches < 1000:
                    self.mismatch_hist["100-999"] += 1
                else:
                    self.mismatch_hist["1000+"] += 1
            if r.error:
                head = r.error.split(":")[0][:80]
                if "DataRace" in r.error:
                    head = "DataRaceError"
                elif "field conflict" in r.error.lower():
                    head = "field conflict"
                self.error_hist[head] += 1
            if r.ok and r.words and r.words < self.best_words:
                self.best_words = r.words
                self.best = r
                self._save_best(r)
            elif r.ok and r.words == self.best_words and self.best is None:
                self.best = r
                self._save_best(r)

    def _family_json(self):
        return {k: dict(v) for k, v in self.family_stats.items()}

    def _save_best(self, r: EvalResult):
        import hashlib
        h = r.hash[:10]
        path = BEST / f"{r.words}w_{h}.vsm"
        text = self.sc.db.execute("SELECT text FROM evals WHERE hash=?",
                                  (r.hash,)).fetchone()[0]
        import zlib
        src = zlib.decompress(text).decode()
        path.write_text(src)
        rec = {"words": r.words, "lines": r.lines, "mismatches": r.mismatches,
               "hash": r.hash, "family": r.family, "chain": r.chain,
               "path": str(path), "ts": time.time()}
        with open(BEST / "log.jsonl", "a") as f:
            f.write(json.dumps(rec) + "\n")
        if self.best_words < 93:
            (BEST / "best.vsm").write_text(src)
        self.log(f"*** NEW BEST words={r.words} ({r.family}) {r.chain} -> {path}")

    def close(self):
        self.log(f"done submitted={self.n_submitted} best={self.best_words}")
        summary = {
            "tag": self.tag, "base_words": 93, "best_words": self.best_words,
            "waves": self.wave_stats,
            "family_stats": self._family_json(),
            "mismatch_hist": dict(self.mismatch_hist),
            "error_hist": dict(self.error_hist.most_common(20)),
            "throughput": self.sc.throughput(),
            "elapsed_s": round(time.time() - self.t_start, 1),
        }
        out = LOGS / f"summary-{self.tag}.json"
        out.write_text(json.dumps(summary, indent=2))
        self.log(f"summary -> {out}")
        self.sc.close()
        self.log_file.close()
        return summary


EvalResult = scorer.EvalResult


# ------------------------------------------------------------------ waves


def wave_seed(c: Campaign):
    c.log("wave seed")
    return c.run_wave("seed", [transforms.Mutation(c.base.clone(), "seed", "baseline")])


def wave_singles(c: Campaign, limit=None, relocate_stride: int = 1):
    """One-step neighbourhood, word-reducing families first.

    `relocate` is the only family with ~8.5k word-neutral members; it is
    sampled (`relocate_stride`) because its sole purpose is to expose
    intermediate states for the plateau wave.
    """
    c.log(f"generating singles (relocate stride {relocate_stride})")
    def gen():
        for fam in ("move_row", "delete", "repair", "merge", "commute",
                    "const", "addr", "noforward", "split", "reorder", "swap"):
            yield from transforms.ALL_FAMILIES[fam](c.base)
        yield from transforms.relocate(c.base, stride=relocate_stride)
    return c.run_wave("singles", gen(), limit=limit)


def wave_moves(c: Campaign, limit=None):
    c.log("generating moves")
    def gen():
        yield from transforms.move_expr(c.base)
        yield from transforms.move_row(c.base)
    return c.run_wave("moves", gen(), limit=limit)


def wave_dissolve(c: Campaign, targets: int = 14, limit=None):
    c.log("generating dissolve")
    return c.run_wave("dissolve", transforms.dissolve(c.base, targets_limit=targets),
                      limit=limit)


def wave_probe(c: Campaign, n: int = 1200, seed: int = 7):
    """Assembler-rejected moves, simulated anyway: failure-mode evidence."""
    c.log(f"probe: simulating {n} assembler-rejected candidates")
    rng = random.Random(seed)
    pool = list(transforms.move_expr(c.base))
    rng.shuffle(pool)
    return c.run_wave("probe_nofilter", iter(pool), limit=n, asm_filter=False)


def wave_anneal(c: Campaign, evals: int = 4000, seed: int = 1, workers_note=""):
    """Simulated annealing that accepts word-neutral moves.

    The primary waves only ever look at words < 93; a word-neutral move is a
    necessary intermediate when no single move packs.  The annealer walks the
    neutral plateau and re-applies every family, keeping the best-ever state
    per word count.  All evaluations go through the scorer cache.
    """
    c.log(f"anneal: {evals} evaluations")
    rng = random.Random(seed)
    cur = c.base.clone()
    cur_words = 93
    best_seen_words = 93
    batch = []
    batch_muts = []
    accepted = 0
    improved = 0
    t0 = time.time()
    for step in range(evals):
        mut = transforms.random_mutation(cur, rng)
        if mut is None:
            continue
        text = mut.program.text()
        batch.append((text, mut.family, " | ".join(mut.program.chain[-4:])))
        batch_muts.append(mut)
        if len(batch) < 200 and step < evals - 1:
            continue
        before = dict(c.sc.stats)
        rs = c.sc.evaluate(batch)
        c.results.extend(rs)
        c.n_submitted += len(batch)
        c._observe(rs)
        # accept moves through the plateau: an OK candidate at equal words is
        # accepted with p=0.5; strictly better word counts always accepted.
        for m, r in zip(batch_muts, rs):
            if r.ok and r.mismatches == 0:
                if r.words < cur_words:
                    cur, cur_words = m.program, r.words
                    accepted += 1
                    improved += 1
                    c.log(f"  anneal improve -> {cur_words}")
                elif r.words == cur_words and rng.random() < 0.5:
                    cur = m.program
                    accepted += 1
        batch, batch_muts = [], []
    wall = time.time() - t0
    c.log(f"anneal: accepted={accepted} improved={improved} wall={wall:.1f}s "
          f"best={c.best_words}")
    return {"wave": "anneal", "evals": evals, "accepted": accepted,
            "improved": improved, "wall_s": round(wall, 1),
            "best_words": c.best_words}


def wave_plateau(c: Campaign, evals: int = 6000, pool_size: int = 48,
                 seed: int = 3, per_seed: int = 2):
    """Neutral-plateau beam search.

    A single move that empties a row is a direct win and was enumerated by
    `moves`/`dissolve`.  A *chain* of moves that only becomes a win at the
    second step needs intermediate states that are semantically correct but
    word-neutral.  Those states are already in the cache: this wave keeps a
    pool of them (words == best, simulator-OK) and samples further mutations
    from the pool, so a two-step dissolution (move one expression out, then the
    other) is within reach.

    Unlike simulated annealing nothing is ever rejected: every OK state is a
    new seed.  The pool is bounded and deduplicated by text hash.
    """
    import zlib

    c.log(f"plateau: {evals} evaluations, pool={pool_size}")
    rng = random.Random(seed)
    # Recover neutral seeds from the cache.
    rows = c.sc.db.execute(
        "SELECT hash, text FROM evals WHERE ok=1 AND stage='sim_ok' "
        "AND words <= ? ORDER BY ts DESC LIMIT 400", (c.best_words,)).fetchall()
    pool = {}
    for h, blob in rows:
        if blob is None:
            continue
        pool[h] = zlib.decompress(blob).decode()
    if c.base_text not in pool.values():
        import hashlib
        pool[hashlib.sha256(c.base_text.encode()).hexdigest()] = c.base_text
    c.log(f"plateau: {len(pool)} seed states")
    # Prioritise seeds that actually moved/partially dissolved a row: their
    # rows differ structurally from the baseline, which is where a second move
    # can still empty a row.  Pure text rewrites (commute/addr/const) are less
    # interesting but are kept as half the pool for diversity.
    from collections import Counter as _Counter
    base_rows = _Counter(_canon_row(r) for r in c.base.rows)
    structural, rest = [], []
    for h, text in pool.items():
        prog = vsmx.parse(text)
        new = [i for i, r in enumerate(prog.rows)
               if not r.nop and _canon_row(r) not in base_rows]
        (structural if new else rest).append(h)
    rng.shuffle(structural)
    rng.shuffle(rest)
    keys = structural[: max(1, pool_size // 2)] + rest[: pool_size]
    keys = keys[:pool_size]
    parsed = {}
    t0 = time.time()
    done = 0
    improved = 0
    batch, batch_meta = [], []
    while done < evals:
        n_this = min(200, evals - done)
        for _ in range(n_this):
            kh = rng.choice(keys)
            prog = parsed.get(kh)
            if prog is None:
                prog = vsmx.parse(pool[kh])
                parsed[kh] = prog
            mut = None
            for _try in range(4):
                m = transforms.random_mutation(prog, rng)
                if m is None:
                    continue
                text = m.program.text()
                if text == pool[kh]:
                    continue
                mut = m
                break
            if mut is None:
                continue
            batch.append(mut.program.text())
            batch_meta.append((mut.family, " | ".join(mut.program.chain[-4:])))
        rs = c.sc.evaluate([(t, f, ch) for t, (f, ch) in zip(batch, batch_meta)])
        c.results.extend(rs)
        c.n_submitted += len(batch)
        c._observe(rs)
        done += len(batch)
        for r, (t, (f, ch)) in zip(rs, zip(batch, batch_meta)):
            if r.ok and r.mismatches == 0 and r.words <= c.best_words:
                if r.hash not in pool:
                    if len(keys) < pool_size:
                        keys.append(r.hash)
                    else:
                        keys[rng.randrange(len(keys))] = r.hash
                    pool[r.hash] = t
                if r.words < 93:
                    improved += 1
        batch, batch_meta = [], []
        if done % 1000 < 200:
            c.log(f"  plateau: {done}/{evals} pool={len(keys)} best={c.best_words} "
                  f"improved={improved}")
    wall = time.time() - t0
    ws = {"wave": "plateau", "evals": done, "pool": len(keys),
          "improved": improved, "wall_s": round(wall, 1),
          "best_words": c.best_words}
    c.wave_stats["plateau"] = ws
    c.log(f"wave plateau: {json.dumps(ws)}")
    return ws


def wave_repair(c: Campaign, limit: int = 600, scan: int = 4000):
    """Turn assembler data-race rejects into neutral states by adding a nop,
    then try to pay for it by deleting a now-unnecessary nop.

    A move rejected with `A racy memory read at ... line L` may be semantically
    correct: the race is a distance problem.  Inserting a nop at L (or moving
    an existing nop there) restores the distance, so the result is a 93-word
    neutral state.  If that state makes some *other* nop unnecessary, deleting
    it gives a 92-word candidate.  This is the one barrier local enumeration
    cannot cross in a single step.
    """
    import hashlib
    import re
    import zlib

    import mncompile.sim as ms

    c.log("repair: scanning assembler-rejected candidates")
    rows = c.sc.db.execute(
        "SELECT text, error FROM evals WHERE stage='asm_error' LIMIT ?",
        (scan,)).fetchall()
    asm = ms.assembler()
    targets = []
    for blob, err in rows:
        if blob is None:
            continue
        text = zlib.decompress(blob).decode()
        a = asm.assemble(text)
        if a.ok:
            continue
        detail = a.error or err or ""
        m = re.search(r"racy memory (?:read|write).*?line (\d+)", detail)
        if not m:
            continue
        # Only word-reducing moves can lead below 93 after paying for one nop.
        # Each row is one line in our emitted programs, so a line count is
        # enough here (a full parse of thousands of programs is slow).
        nrows = sum(1 for line in text.splitlines() if line.strip())
        if nrows >= 93:
            continue
        targets.append((text, int(m.group(1))))
        if len(targets) >= limit:
            break
    if asm.cache:
        asm.cache.clear()
    c.log(f"repair: {len(targets)} data-race candidates to repair")

    muts = []
    for text, line in targets:
        prog = vsmx.parse(text)
        for pos, where in ((line - 1, "before"), (line, "after")):
            if 0 <= pos <= len(prog.rows):
                rr = list(prog.rows)
                rr.insert(pos, vsmx.make_nop_row())
                muts.append(transforms.Mutation(
                    prog.clone(rows=rr,
                               chain_add=f"repair_race/nop@{pos + 1}({where} line {line})"),
                    "repair_race", f"nop@{pos + 1}"))
        # alternative: move an existing nop to the race site (word-neutral)
        nops = [i for i, r in enumerate(prog.rows) if r.nop]
        for ni in nops[:2]:
            rr = list(prog.rows)
            nop = rr.pop(ni)
            at = line - 1 if ni > line - 1 else line - 1
            at = max(0, min(at, len(rr)))
            rr.insert(at, nop)
            muts.append(transforms.Mutation(
                prog.clone(rows=rr,
                           chain_add=f"repair_race/move_nop L{ni + 1}->{at + 1}"),
                "repair_race", f"move_nop L{ni + 1}->{at + 1}"))
    c.run_wave("repair_race", iter(muts))

    # phase 2: for neutral repaired states, try deleting each nop
    dels = []
    for m in muts:
        h = hashlib.sha256(m.program.text().encode()).hexdigest()
        row = c.sc.get(h)
        if row is None:
            continue
        stage, ok, words, lines, mis, err, asm_words = row
        if not ok or words != 93:
            continue
        for i, r in enumerate(m.program.rows):
            if not r.nop:
                continue
            rr = vsmx.drop_row(m.program.rows, i)
            dels.append(transforms.Mutation(
                m.program.clone(rows=rr, chain_add=f"repair_race/delete_nop L{i + 1}"),
                "repair_race_delete", f"L{i + 1}"))
    c.log(f"repair: {len(dels)} nop-deletion follow-ups")
    if dels:
        c.run_wave("repair_race_delete", iter(dels))
    return c.wave_stats.get("repair_race"), c.wave_stats.get("repair_race_delete")


def _canon_row(row) -> str:
    if row.nop:
        return f"nop/{row.nop}"
    return "; ".join(i.text() for i in row.instrs)


def wave_finish(c: Campaign, seeds: int = 200, max_rows: int = 3):
    """Finish the partial dissolutions discovered by the `moves` wave.

    The moves wave left several neutral 93-word states in which one expression
    of a two-expression row was moved into another row, but the row itself
    survived (one expression left) so no word was saved.  Here each such
    "new" row (its canonical text does not occur in the baseline) is dissolved
    completely: delete it, move its remaining expressions, or move the whole
    row.  A success is a 92-word candidate.
    """
    import zlib
    from collections import Counter

    base_rows = Counter(_canon_row(r) for r in c.base.rows)
    rows = c.sc.db.execute(
        "SELECT hash, text FROM evals WHERE ok=1 AND stage='sim_ok' AND words=93"
    ).fetchall()
    picked = []
    for h, blob in rows:
        if blob is None:
            continue
        prog = vsmx.parse(zlib.decompress(blob).decode())
        new = [i for i, r in enumerate(prog.rows)
               if not r.nop and _canon_row(r) not in base_rows]
        if new:
            picked.append((len(new), h, prog, new))
    picked.sort(key=lambda x: x[0])
    c.log(f"finish: {len(picked)} partial-dissolution seeds")
    muts = []

    def gen():
        for n_new, h, prog, new in picked[:seeds]:
            prog.chain = (f"seed:{h[:8]}",)
            src = set(new[:max_rows])
            yield from transforms.delete(prog, src_rows=src)
            yield from transforms.move_expr(prog, src_rows=src)
            yield from transforms.move_row(prog, src_rows=src)
    return c.run_wave("finish", gen())


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--tag", default="main")
    ap.add_argument("--waves", default="seed,singles,moves,dissolve")
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--dissolve-targets", type=int, default=14)
    ap.add_argument("--anneal-evals", type=int, default=4000)
    ap.add_argument("--plateau-evals", type=int, default=6000)
    ap.add_argument("--probe-n", type=int, default=1200)
    ap.add_argument("--relocate-stride", type=int, default=8)
    ap.add_argument("--repair-limit", type=int, default=600)
    ap.add_argument("--finish-seeds", type=int, default=200)
    args = ap.parse_args(argv)

    c = Campaign(args.workers, tag=args.tag)
    c.log(f"start tag={args.tag} workers={args.workers} waves={args.waves}")
    waves = [w.strip() for w in args.waves.split(",") if w.strip()]
    for w in waves:
        if w == "seed":
            wave_seed(c)
        elif w == "singles":
            wave_singles(c, args.limit, args.relocate_stride)
        elif w == "moves":
            wave_moves(c, args.limit)
        elif w == "dissolve":
            wave_dissolve(c, args.dissolve_targets, args.limit)
        elif w == "probe":
            wave_probe(c, args.probe_n)
        elif w == "anneal":
            wave_anneal(c, args.anneal_evals)
        elif w == "plateau":
            wave_plateau(c, args.plateau_evals)
        elif w == "repair":
            wave_repair(c, args.repair_limit)
        elif w == "finish":
            wave_finish(c, args.finish_seeds)
        else:
            raise SystemExit(f"unknown wave {w}")
    summary = c.close()
    print(json.dumps(summary, indent=2)[:4000])


if __name__ == "__main__":
    main()
