#!/usr/bin/env python3
"""Abstract lower bound for the final 4096-long-word delivery to Group 0 DRAM.

The model counts *assembled words* (one j or m line per step).  It is the
abstract version of the FizzBuzz output stage; the constants are the SDM
capacities and the assembler-enforced hazard gaps (see README.md).

Actions and capacities (long words moved per word):
  L1WRITE : PE -> L1BM via l1bmd             16384 = 64 PEs * 4 cyc * 64 L1B
  L2WRITE : L1BM -> L2BM via l2bmd           2048  = 64 w/cyc * 4 cyc * 8 L2BM
  GATHER  : L2BM -> PDM via mvd/n512         4096  = 512 w/L2B * 8 L2B
  DRAM_PDM: PDM -> DRAM via mvp/n4096        4096
  DRAM_L2 : L2BM -> DRAM (one L2B only)      4096 with >=16 L2WRITE words
Hazards (verified with assemble3; see logs/probe_isa.txt):
  L2WRITE at s requires s >= L1WRITE + 3     (2 intervening words)
  GATHER/DRAM_L2 at s requires s >= last L2WRITE + 2 (1 intervening word)
  DRAM_PDM at s requires s >= GATHER + 1     (0 intervening words)

Initial state: the 4096 output words are already resident in PE-side storage
(GRF/LM/T); all other memories zero.  Goal: all 4096 words in Group 0 DRAM.
"""
from __future__ import annotations
import argparse
from collections import deque

NOP, L1W, L2W, GATHER, DRAM_PDM, DRAM_L2 = range(6)
NAMES = {NOP:"nop", L1W:"l1bmd(PE->L1BM)", L2W:"l2bmd(L1BM->L2BM)",
         GATHER:"mvd/n512(L2BM->PDM)", DRAM_PDM:"mvp/n4096(PDM->DRAM)",
         DRAM_L2:"mvp/n4096(L2BM->DRAM)"}

# State: (l1_done, l1_t, l2n, last_l2, pdm, dram); t is the layer index.
def initial():
    return (0, -1, 0, -1, 0, 0)

def step(st, t, act):
    l1_done, l1_t, l2n, last_l2, pdm, dram = st
    if act == NOP:
        return st
    if act == L1W:
        if l1_done:
            return None
        return (1, t, l2n, last_l2, pdm, dram)
    if act == L2W:
        if not l1_done or t < l1_t + 3 or l2n >= 16:
            return None
        return (l1_done, l1_t, l2n + 1, t, pdm, dram)
    if act == GATHER:
        if last_l2 < 0 or t < last_l2 + 2 or l2n < 2:
            return None
        return (l1_done, l1_t, l2n, last_l2, 1, dram)
    if act == DRAM_PDM:
        if not pdm:
            return None
        return (l1_done, l1_t, l2n, last_l2, pdm, 1)
    if act == DRAM_L2:
        if last_l2 < 0 or t < last_l2 + 2 or l2n < 16:
            return None
        return (l1_done, l1_t, l2n, last_l2, pdm, 1)
    raise ValueError(act)

def bfs(max_t=30):
    """Return (min_t, path, layer_sizes) or (None, None, layers)."""
    start = initial()
    q = deque([(start, 0, [])])
    seen = {(0, start)}
    layers = []
    while q:
        st, t, path = q.popleft()
        if len(layers) <= t:
            layers.append(0)
        layers[t] += 1
        if st[5]:
            return t, path, layers
        if t >= max_t:
            continue
        for act in range(6):
            ns = step(st, t, act)
            if ns is None:
                continue
            if (t + 1, ns) not in seen:
                seen.add((t + 1, ns))
                q.append((ns, t + 1, path + [(t, act)]))
    return None, None, layers

def build_layer_tables(K):
    """All reachable states per layer and the allowed (s_t, s_{t+1}) pairs."""
    cur = {initial(): None}
    layers = [cur]
    for t in range(K):
        nxt = {}
        for st in cur:
            for act in range(6):
                ns = step(st, t, act)
                if ns is not None:
                    nxt[ns] = None
        layers.append(nxt)
        cur = nxt
    # encode
    def enc(st): return (((((st[0] * 32 + (st[1] + 1)) * 17 + st[2]) * 32 + (st[3] + 1)) * 2 + st[4]) * 2 + st[5])
    table = []
    for t in range(K):
        pairs = set()
        for st in layers[t]:
            for act in range(6):
                ns = step(st, t, act)
                if ns is not None and ns in layers[t + 1]:
                    pairs.add((enc(st), enc(ns)))
        table.append(sorted(pairs))
    return layers, table, enc

def solve_cpsat(K, time_limit=120.0):
    from ortools.sat.python import cp_model
    layers, table, enc = build_layer_tables(K)
    model = cp_model.CpModel()
    s = [model.NewIntVar(0, 2**31 - 1, f"s{t}") for t in range(K + 1)]
    model.Add(s[0] == enc(initial()))
    for t in range(K):
        model.AddAllowedAssignments([s[t], s[t + 1]], table[t])
    # Constrain the final state to *any* dram=1 state; the layer transition
    # tables (not a precomputed reachable-goal set) must prove reachability.
    goals = []
    for l1d in (0, 1):
        for l1t in range(-1, K):
            for l2n in range(17):
                for last in range(-1, K):
                    for pdm in (0, 1):
                        goals.append(enc((l1d, l1t, l2n, last, pdm, 1)))
    model.AddAllowedAssignments([s[K]], [[g] for g in sorted(set(goals))])
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = time_limit
    solver.parameters.num_search_workers = 1
    status = solver.Solve(model)
    status_name = solver.StatusName(status)
    path = None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        dec = {v: k for k, v in enc_dict(layers).items()}
        path = [dec[solver.Value(s[t])] for t in range(K + 1)]
    return status_name, path, layers, table, enc, (solver.WallTime(), solver.NumBranches(), solver.NumConflicts())

def brute_force(K):
    """Independent exhaustive search over all 6^K action sequences."""
    import itertools
    for seq in itertools.product(range(6), repeat=K):
        st = initial()
        for t, act in enumerate(seq):
            st = step(st, t, act)
            if st is None:
                break
        if st is not None and st[5]:
            return seq
    return None


def enc_dict(layers):
    d = {}
    for layer in layers:
        for st in layer:
            d[st] = (((((st[0] * 32 + (st[1] + 1)) * 17 + st[2]) * 32 + (st[3] + 1)) * 2 + st[4]) * 2 + st[5])
    return d

def path_to_actions(path):
    out = []
    for i in range(len(path) - 1):
        for act in range(6):
            if step(path[i], i, act) == path[i + 1]:
                out.append((i, act)); break
        else:
            out.append((i, None))
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="run BFS + CP-SAT checks")
    ap.add_argument("--max-k", type=int, default=8)
    a = ap.parse_args()
    min_t, path, layers = bfs()
    print("BFS shortest delivery length:", min_t)
    if path:
        for t, act in path:
            print(f"  t={t:2d}  {NAMES[act]}")
    print("BFS reachable states per layer:", layers[:min_t + 1])
    if a.check:
        print("\nbrute force, K=7 (all 6^7 action sequences):",
              "NO PLAN" if brute_force(7) is None else "PLAN FOUND")
        for K in range(7, 9):
            status, cpath, _, _, _, stats = solve_cpsat(K)
            print(f"CP-SAT K={K}: {status}  wall={stats[0]:.3f}s branches={stats[1]} conflicts={stats[2]}")
            if cpath:
                for t, act in path_to_actions(cpath):
                    print(f"  t={t:2d}  {NAMES[act]}")
        assert min_t == 8, f"unexpected BFS bound {min_t}"
        assert brute_force(7) is None, "K=7 brute force found a plan"
        status7, _, _, _, _, _ = solve_cpsat(7)
        status8, _, _, _, _, _ = solve_cpsat(8)
        assert status7 == "INFEASIBLE", f"K=7 must be UNSAT, got {status7}"
        assert status8 in ("OPTIMAL", "FEASIBLE"), f"K=8 must be SAT, got {status8}"
        print("ALL CHECKS PASSED: delivery minimum 8 (K=7 UNSAT, K=8 SAT)")

if __name__ == "__main__":
    main()
