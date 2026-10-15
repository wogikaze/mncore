"""Contractions on the matrix unit.

An output tensor whose elements are sums of products of two input elements,
C[o] = sum_k U[f(o, k)] * V[g(o, k)], is analysed into free axes (U's index
taken from the output), contracted axes (shared by U and V, varying inside one
output) and batch axes (shared by U, V and C). When the contracted axis of an
operand lies on the PE/lane axes of a MAB, the operand can be the vector of a
matrix-vector product, or (written row by row) the matrix register. An operand
whose contracted axis lies on the address axis is first transposed through the
matrix register (rows written, columns read back).

Block-float conversion is required for the multiplicand inputs; its precision
is checked by verification (exact for small integers).
"""

from __future__ import annotations

import math
from collections import defaultdict
from dataclasses import dataclass, field

from .errors import CompileError
from .ir import Node
from .layout import Contract, TensorSpec, pe_coords
from .machine import Fixed, Mat, Mem
from .vprog import Use, Value, VOp, VProgram


@dataclass
class Contraction:
    out: TensorSpec
    u: TensorSpec
    v: TensorSpec
    u_free: dict  # U axis -> output axis
    v_free: dict  # V axis -> output axis
    u_k: list  # contracted U axes
    v_k: list  # contracted V axes (same order: u_k[i] pairs with v_k[i])
    batch: list  # output axes that are free in both U and V


def _factor_pairs(node: Node):
    if node.op != "sum" and node.op != "mul":
        raise CompileError("contraction: output is not a sum of products")
    terms = node.args if node.op == "sum" else (node,)
    pairs = []
    for t in terms:
        if t.op != "mul" or len(t.args) != 2 or any(a.op != "input" for a in t.args):
            raise CompileError("contraction: term is not a product of two inputs")
        pairs.append((t.args[0].value, t.args[1].value))
    return pairs


def analyze_contraction(contract: Contract, outputs: dict) -> Contraction:
    if len(contract.outputs) != 1:
        raise CompileError("contraction: one output tensor")
    out = contract.outputs[0]
    items = list(outputs[out.name].items())
    specs = {s.name: s for s in contract.inputs}
    tensors = set()
    for _, node in items[:: max(1, len(items) // 64)][:64]:
        for a, b in _factor_pairs(node):
            tensors.update([a[0], b[0]])
    if len(tensors) > 2:
        raise CompileError("contraction: more than two tensors")
    names = sorted(tensors)
    same = len(names) == 1
    un, vn = (names[0], names[0]) if same else (names[0], names[1])

    def maps(idx, o):
        return {(a, b) for a in range(len(idx)) for b in range(len(o)) if idx[a] == o[b]}

    def pattern(idx, o):
        return tuple(next((b for b in range(len(o)) if idx[a] == o[b]), None) for a in range(len(idx)))

    clean = [(o, n) for o, n in items if len(set(o)) == len(o)] or items
    sample = clean[:: max(1, len(clean) // 64)][:64]
    u_pat = None
    if same:
        counts = defaultdict(int)
        for o, node in sample[:8]:
            for a, b in _factor_pairs(node):
                if a[1][len(a[1]) - 1] not in o or True:
                    counts[pattern(a[1], o)] += 1
                    counts[pattern(b[1], o)] += 1
        u_pat = max(counts, key=counts.get)
    u_map = v_map = None
    uv = None
    for o, node in sample:
        pairs = _factor_pairs(node)
        for a, b in pairs:
            if not same:
                fu, fv = (a, b) if a[0] == un else (b, a)
            else:
                pa, pb = pattern(a[1], o), pattern(b[1], o)
                if pa == u_pat and pb != u_pat:
                    fu, fv = a, b
                elif pb == u_pat and pa != u_pat:
                    fu, fv = b, a
                else:
                    continue  # ambiguous term (coincident coordinates); skip in the analysis
            mu, mv = maps(fu[1], o), maps(fv[1], o)
            u_map = mu if u_map is None else u_map & mu
            v_map = mv if v_map is None else v_map & mv
            muv = {(i, j) for i in range(len(fu[1])) for j in range(len(fv[1])) if fu[1][i] == fv[1][j]}
            uv = muv if uv is None else uv & muv
    if u_map is None:
        raise CompileError("contraction: no unambiguous terms")
    U, V = specs[un], specs[vn]
    u_free = {}
    for a, b in sorted(u_map):
        u_free.setdefault(a, b)
    v_free = {}
    for a, b in sorted(v_map):
        v_free.setdefault(a, b)
    u_k = [a for a in range(len(U.shape)) if a not in u_free]
    v_k = [a for a in range(len(V.shape)) if a not in v_free]
    pairs_k = [(i, j) for i, j in sorted(uv) if i in u_k and j in v_k]
    if len(u_k) != 1 or len(v_k) != 1 or (u_k[0], v_k[0]) not in pairs_k:
        raise CompileError(f"contraction: unsupported index structure u_free={u_free} v_free={v_free} uv={uv}")
    batch = sorted(set(u_free.values()) & set(v_free.values()))
    # free axes of one operand that lie on the hierarchy (L2B/L1B/MAB) where the other operand is
    # broadcast: every unit computes its own block, like a batch axis
    hier = ("L2B", "L1B", "MAB")
    for own, other, free in ((U, V, u_free), (V, U, v_free)):
        bcast = {d.axis for d in other.layout.broadcast}
        for a, b in list(free.items()):
            dims = own.layout.axes[a]
            if b in batch or not dims or not all(d.axis in hier for d in dims):
                continue
            if [(d.size, d.axis, d.stride) for d in dims] != [(d.size, d.axis, d.stride) for d in out.layout.axes[b]]:
                continue
            if all(d.axis in bcast for d in dims):
                batch.append(b)
    batch = sorted(set(batch))
    k_size = U.shape[u_k[0]]
    for o, node in sample:
        if len(_factor_pairs(node)) != k_size:
            raise CompileError("contraction: terms do not cover the contracted axis")
    return Contraction(out, U, V, u_free, v_free, u_k, v_k, batch)


def axis_dims(spec: TensorSpec, axis: int):
    return spec.layout.axes[axis]


def on_vector_axes(dims) -> bool:
    return all(d.axis in ("PE", "W") for d in dims)


def vector_dims(dims):
    return [d for d in dims if d.axis in ("PE", "W")]


# ---------------------------------------------------------------- code generation

def _addr_of(spec: TensorSpec, index):
    """Long word address and vector position (pe, b, lane) of a logical element (first replica)."""
    pos = spec.positions(index)
    return spec.base_long + pos.get("", 0), pos.get("PE", 0), pos.get("W", 0)


def _vector_position(spec: TensorSpec, axis: int, value: int):
    """(pe, b, lane, address part) contributed by one axis value."""
    contrib = spec._axis_positions(spec.layout.axes[axis], value)
    return contrib.get("PE", 0), contrib.get("W", 0), contrib.get("", 0)


@dataclass
class Mode:
    name: str  # "g" (8x8 pseudo-single) or "h" (16x16 half)
    k: int  # contraction length per MAB vector
    rows: int  # matrix rows
    out_words: int  # output long words per PE per cycle


GM = Mode("g", 8, 8, 1)
HM = Mode("h", 16, 16, 2)


def contraction_strategy(source, contract: Contract, outputs: dict, *, variant=None):
    cn = analyze_contraction(contract, outputs)
    out, U, V = cn.out, cn.u, cn.v
    if out.dtype.name != "Float" or U.dtype.name != "Float" or V.dtype.name != "Float":
        raise CompileError("contraction: only Float data so far")
    for ax in cn.batch:
        if any(d.axis in ("", "W", "PE") for d in out.layout.axes[ax]):
            raise CompileError("contraction: batch axis must lie on L2B/L1B/MAB")
        for spec, free in ((U, cn.u_free), (V, cn.v_free)):
            sax = next((a for a, b in free.items() if b == ax), None)
            if sax is None:
                continue  # broadcast over this hierarchy axis (checked by the analysis)
            if [(d.size, d.axis, d.stride) for d in spec.layout.axes[sax]] != [(d.size, d.axis, d.stride) for d in out.layout.axes[ax]]:
                raise CompileError("contraction: batch axis placed differently")
    ua = next(b for a, b in cn.u_free.items() if b not in cn.batch)
    va = next(b for a, b in cn.v_free.items() if b not in cn.batch)
    out_vec_axis = [a for a in (ua, va) if any(d.axis in ("PE", "W") for d in out.layout.axes[a])]
    if len(out_vec_axis) != 1:
        raise CompileError("contraction: output needs one free axis on PE/lane axes")
    f_vec = out_vec_axis[0]
    f_addr = ua if f_vec == va else va
    m_is_v = f_vec == va
    mop, xop = (V, U) if m_is_v else (U, V)
    mk = cn.v_k[0] if m_is_v else cn.u_k[0]
    xk = cn.u_k[0] if m_is_v else cn.v_k[0]
    mfree_map = cn.v_free if m_is_v else cn.u_free
    xfree_map = cn.u_free if m_is_v else cn.v_free
    mfree = next(a for a, b in mfree_map.items() if b == f_vec)
    xfree = next(a for a, b in xfree_map.items() if b == f_addr)
    K = mop.shape[mk]
    variants = []
    direct = all(_is_vec(spec, k) for spec, k in ((mop, mk), (xop, xk)))
    if K == 16 and direct:
        try:
            variants.append(("hm", _gen(cn, out, mop, xop, mk, xk, mfree, xfree, f_vec, f_addr, "h")))
        except CompileError:
            pass
    if K in (8, 16) and direct:
        try:
            variants.append(("gm-direct", _gen(cn, out, mop, xop, mk, xk, mfree, xfree, f_vec, f_addr, "g")))
        except CompileError:
            pass
    if K == 16:
        try:
            variants.append(("hm-t", _gen_ht(cn, out, mop, xop, mk, xk, mfree, xfree, f_vec, f_addr)))
            variants.append(("hm-t-bfn", _gen_ht(cn, out, mop, xop, mk, xk, mfree, xfree, f_vec, f_addr, "hbfn/9")))
        except CompileError:
            pass
    try:
        variants.append(("gm", _gen_g(cn, out, mop, xop, mk, xk, mfree, xfree, f_vec, f_addr)))
    except CompileError as exc:
        if not variants:
            raise

    if not variants:
        raise CompileError(f"contraction: contraction length {K} not supported")
    return variants


def _k_half(spec, k, value):
    """(pe, lane, address part) of contracted index `value` in an operand."""
    return _vector_position(spec, k, value)


def _gen(cn, out, mop, xop, mk, xk, mfree, xfree, f_vec, f_addr, prec):
    from .machine import Mask

    prog = VProgram()
    K = mop.shape[mk]
    if prec == "h":
        rows_per = 16
        # one matrix, contraction over 16 = 4 PEs x (2 long words x 2 lanes)
        halves = [0]
    else:
        rows_per = 8
        halves = sorted({_k_half(mop, mk, kk)[2] for kk in range(K)})
        if len(halves) > 2 or {_k_half(xop, xk, kk)[2] for kk in range(K)} != set(halves):
            raise CompileError("contraction: contracted axis layout differs between operands")
    # matrix rows: output vector position -> f_vec index
    row_of = {}
    for j in range(out.shape[f_vec]):
        pe, lane, a = _vector_position(out, f_vec, j)
        if prec == "h":
            row_of[(0, 4 * pe + 2 * a + lane)] = j
        else:
            row_of[(a, 2 * pe + lane)] = j
    blocks = sorted({m for m, _ in row_of})
    if prec == "h" and any(r >= 16 for _, r in row_of):
        raise CompileError("contraction: too many rows")
    mats = [(m, h) for m in blocks for h in halves]
    batches = [mats[i:i + 2] for i in range(0, len(mats), 2)]
    # vector rows: one per distinct local row of the vector operand
    rows = {}
    for i in range(out.shape[f_addr]):
        idx = [0] * len(xop.shape)
        idx[xfree] = i
        xa, _, _ = _addr_of(xop, tuple(idx))
        oidx = [0] * len(out.shape)
        oidx[f_addr] = i
        dsts = []
        for m in blocks:
            jrow = next(v for (mm, r), v in sorted(row_of.items()) if mm == m)
            oidx[f_vec] = jrow
            oa, _, _ = _addr_of(out, tuple(oidx))
            pe, lane, apart = _vector_position(out, f_vec, jrow)
            dsts.append(oa - apart + (m if prec == "g" else 0))
        if rows.setdefault(xa, dsts) != dsts:
            raise CompileError("contraction: rows with one address map to different outputs")
    order = sorted(rows.items(), key=lambda kv: kv[1])
    used_words = 1 if prec == "g" else (2 if any((r // 2) % 2 for _, r in row_of) else 1)
    groups = []
    for g0 in range(0, len(order), 4):
        chunk = order[g0:g0 + 4]
        live = len(chunk)
        while len(chunk) < 4:
            chunk = chunk + [chunk[-1]]
        groups.append((chunk, live))
    # BF'd vectors per group and contraction half (address offset h inside the row)
    xbf = {}
    last_readers = {"x": [], "y": []}
    for b_i, batch in enumerate(batches):
        side_of = {mat: side for mat, side in zip(batch, ["y", "x"])}
        tokens = {side: [] for side in side_of.values()}
        for (m, h), side in side_of.items():
            ordered = [row_of.get((m, r)) for r in range(rows_per)]
            for r0 in range(0, rows_per, 4):
                chunk = ordered[r0:r0 + 4]
                addrs = []
                for j in chunk:
                    if j is None:
                        addrs.append(None)
                        continue
                    idx = [0] * len(mop.shape)
                    idx[mfree] = j
                    a, _, _ = _addr_of(mop, tuple(idx))
                    addrs.append(a + h)
                live = [a for a in addrs if a is not None]
                if not live:
                    continue
                addrs = [a if a is not None else live[0] for a in addrs]
                if prec == "g":
                    bf = VOp("gbfn", [Mem(mop.space, 2, tuple(a * 2 for a in addrs))], out=Value(2), unit="alu")
                else:
                    bf = VOp("hbfn/9", [Mem(mop.space, 4, tuple(a * 2 for a in addrs), rnd=True)], out=Value(2), unit="alu")
                prog.add(bf)
                tok = Value(0, "mat")
                tok.nofwd = True
                prog.add(VOp(f"{prec}mwrite", [Use(bf.out)], out=tok, dsts=[Mat(side, r0)], unit="mwrite", after=list(last_readers[side])))
                tokens[side].append(tok)
        for side in side_of.values():
            last_readers[side] = []
        for chunk, live in groups:
            for m in sorted({m for m, _ in batch}):
                chain = [(h, side_of[(m, h)]) for h in halves if (m, h) in side_of]
                acc = None
                for n, (h, side) in enumerate(chain):
                    key = (tuple(xa for xa, _ in chunk), h)
                    if key not in xbf:
                        xaddrs = [xa + h for xa, _ in chunk]
                        if prec == "g":
                            bf = VOp("gbfn", [Mem(xop.space, 2, tuple(a * 2 for a in xaddrs))], out=Value(2), unit="alu")
                        else:
                            bf = VOp("hbfn/9", [Mem(xop.space, 4, tuple(a * 2 for a in xaddrs), rnd=True)], out=Value(2), unit="alu")
                        prog.add(bf)
                        xbf[key] = bf.out
                    last = n == len(chain) - 1
                    dsts = []
                    if last:
                        daddrs = [d[blocks.index(m)] for _, d in chunk]
                        wl = 2 * used_words
                        mask = None if live == 4 else Mask(pattern="1" * live + "0" * (4 - live), ll=(wl == 4))
                        dsts = [Mem(out.space, wl, tuple(a * 2 for a in daddrs), mask=mask)]
                    tok = Value(0, "mm")
                    tok.nofwd = True
                    if acc is None:
                        vop = VOp(f"{prec}mmul", [Mat(side), Use(xbf[key])], out=None if last else Value(4), dsts=dsts, unit="mau", after=list(tokens[side]))
                    else:
                        vop = VOp(f"{prec}mfma", [Mat(side), Use(xbf[key]), Use(acc)], out=None if last else Value(4), dsts=dsts, unit="mau", after=list(tokens[side]))
                    prog.add(vop)
                    acc = vop.out
                    marker = VOp("noforward", [], unit="marker") if False else None
                    last_readers[side].append(vop.out or _token_for(prog, vop))
    return prog


def _token_for(prog, vop):
    """A value representing completion of `vop` (for ordering later matrix writes)."""
    tok = Value(0, "done")
    tok.nofwd = True
    vop.flags_out = None
    if vop.out is None:
        vop.out = tok
        return tok
    return vop.out


# ---------------------------------------------------------------- general gm generator with transposes

def _kpos_from(spec, axis, K):
    """Contracted index -> (half, vector position) from an operand whose axis is on PE/lanes."""
    parts = sorted({_vector_position(spec, axis, k)[2] for k in range(K)})
    out = {}
    for k in range(K):
        pe, lane, a = _vector_position(spec, axis, k)
        out[k] = (parts.index(a), 2 * pe + lane)
    return out


def _is_vec(spec, axis):
    dims = spec.layout.axes[axis]
    return any(d.axis == "PE" for d in dims) and all(d.axis in ("PE", "W", "") for d in dims)


def _is_addr(spec, axis):
    return all(d.axis == "" for d in spec.layout.axes[axis])


class _Side:
    def __init__(self, name):
        self.name = name
        self.writers = []
        self.readers = []

    def write_after(self):
        return list(self.readers) + list(self.writers)

    def read_after(self):
        return list(self.writers)


def _gen_g(cn, out, mop, xop, mk, xk, mfree, xfree, f_vec, f_addr):
    from .machine import Mask

    prog = VProgram()
    K = mop.shape[mk]
    m_direct, x_direct = _is_vec(mop, mk), _is_vec(xop, xk)
    if not (m_direct or _is_addr(mop, mk)) or not (x_direct or _is_addr(xop, xk)):
        raise CompileError("contraction: contracted axis is mixed")
    if not m_direct and not _is_vec(mop, mfree):
        raise CompileError("contraction: transposed matrix operand needs its free axis on PE/lanes")
    if not x_direct and not _is_vec(xop, xfree):
        raise CompileError("contraction: transposed vector operand needs its free axis on PE/lanes")
    kpos = None
    if x_direct:
        kpos = _kpos_from(xop, xk, K)
    elif m_direct:
        kpos = _kpos_from(mop, mk, K)
    else:
        kpos = {k: (k // 8, k % 8) for k in range(K)}
    if kpos is None:
        raise CompileError("contraction: contracted axis does not fit two halves")
    for spec, ax, direct in ((mop, mk, m_direct), (xop, xk, x_direct)):
        if direct and _kpos_from(spec, ax, K) != kpos:
            raise CompileError("contraction: operands place the contracted axis differently")
    halves = sorted({h for h, _ in kpos.values()})
    # output rows of the matrix-vector product
    row_of = {}
    for j in range(out.shape[f_vec]):
        pe, lane, a = _vector_position(out, f_vec, j)
        row_of[(a, 2 * pe + lane)] = j
    blocks = sorted({m for m, _ in row_of})
    any_t = not (m_direct and x_direct)
    sides = {"y": _Side("y"), "x": _Side("x")}

    def addr(spec, axis_vals):
        idx = [0] * len(spec.shape)
        for ax, v in axis_vals.items():
            idx[ax] = v
        a, _, _ = _addr_of(spec, tuple(idx))
        return a

    # transposition blocks: (operand tag, half, free block) -> {column: vector-producing op}
    def plain_rows(spec, kax, fax, h, fblock):
        """Write the rows of one 8x8 block (k in half h) of a k-on-address operand to the scratch side."""
        side = sides["y"]
        ks = sorted(k for k, (hh, r) in kpos.items() if hh == h)
        rows = {kpos[k][1]: k for k in ks}
        toks = []
        for r0 in (0, 4):
            ad = []
            for r in range(r0, r0 + 4):
                k = rows.get(r)
                ad.append(None if k is None else addr(spec, {kax: k}) + fblock)
            live = [a for a in ad if a is not None]
            if not live:
                continue
            ad = [a if a is not None else live[0] for a in ad]
            tok = Value(0, "mw")
            tok.nofwd = True
            prog.add(VOp("gmwrite", [Mem(spec.space, 2, tuple(a * 2 for a in ad))], out=tok, dsts=[Mat("y", r0)], unit="mwrite", after=side.write_after()))
            toks.append(tok)
        side.writers = toks
        side.readers = []

    def read_columns(c0):
        side = sides["y"]
        v = VOp("gmread", [Mat("y", c0)], out=Value(2), unit="mread", after=side.read_after())
        prog.add(v)
        side.readers.append(v.out)
        return v.out

    def bf(src):
        v = VOp("gbfn", [src], out=Value(2), unit="alu")
        prog.add(v)
        return v.out

    final_side = sides["x"] if any_t else None
    mats = [(m, h) for m in blocks for h in halves]
    # rows of the vector operand, grouped four per op
    rows_x = {}
    for i in range(out.shape[f_addr]):
        if x_direct:
            key = addr(xop, {xfree: i})
        else:
            pe, lane, a = _vector_position(xop, xfree, i)
            key = (a, 2 * pe + lane)
        dsts = []
        for m in blocks:
            jrow = next(v for (mm, r), v in sorted(row_of.items()) if mm == m)
            oidx = {f_addr: i, f_vec: jrow}
            pe, lane, apart = _vector_position(out, f_vec, jrow)
            dsts.append(addr(out, oidx) - apart + m)
        if rows_x.setdefault(key, dsts) != dsts:
            raise CompileError("contraction: rows with one address map to different outputs")
    if x_direct:
        order = sorted(rows_x.items(), key=lambda kv: kv[1])
        groups = []
        for g0 in range(0, len(order), 4):
            chunk = order[g0:g0 + 4]
            live = len(chunk)
            groups.append((chunk + [chunk[-1]] * (4 - live), live))
    else:
        # transposed: a group is four consecutive columns of one free block
        by_block = defaultdict(dict)
        for (fb, c), d in rows_x.items():
            by_block[fb][c] = d
        groups = []
        for fb, cols in sorted(by_block.items()):
            for c0 in range(0, 8, 4):
                chunk = [((fb, c), cols[c]) for c in range(c0, c0 + 4) if c in cols]
                if not chunk:
                    continue
                if [k[1] for k, _ in chunk] != list(range(c0, c0 + len(chunk))):
                    raise CompileError("contraction: transposed rows are not consecutive columns")
                live = len(chunk)
                groups.append((chunk + [chunk[-1]] * (4 - live), live))
    acc = {}
    for mi, (m, h) in enumerate(mats):
        side = final_side or sides["y" if mi % 2 == 0 else "x"]
        # --- load the matrix for (m, h)
        ordered = [row_of.get((m, r)) for r in range(8)]
        if m_direct:
            toks = []
            hpart = sorted({_vector_position(mop, mk, k)[2] for k in range(K)})[h]
            for r0 in (0, 4):
                chunk = ordered[r0:r0 + 4]
                ad = [None if j is None else addr(mop, {mfree: j}) + hpart for j in chunk]
                live = [a for a in ad if a is not None]
                if not live:
                    continue
                ad = [a if a is not None else live[0] for a in ad]
                v = bf(Mem(mop.space, 2, tuple(a * 2 for a in ad)))
                tok = Value(0, "mw")
                tok.nofwd = True
                prog.add(VOp("gmwrite", [Use(v)], out=tok, dsts=[Mat(side.name, r0)], unit="mwrite", after=side.write_after()))
                toks.append(tok)
            side.writers = toks
            side.readers = []
        else:
            # rows of the final matrix are columns of the transposed operand
            fblocks = sorted({_vector_position(mop, mfree, j)[2] for j in ordered if j is not None})
            if len(fblocks) != 1:
                raise CompileError("contraction: matrix rows span several free blocks")
            plain_rows(mop, mk, mfree, h, fblocks[0])
            toks = []
            for r0 in (0, 4):
                chunk = ordered[r0:r0 + 4]
                cols = [None if j is None else 2 * _vector_position(mop, mfree, j)[0] + _vector_position(mop, mfree, j)[1] for j in chunk]
                if any(c is not None and c != r0 + n for n, c in enumerate(cols)):
                    raise CompileError("contraction: transposed rows would need a permutation")
                if all(c is None for c in cols):
                    continue
                vec = bf(Use(read_columns(r0)))
                tok = Value(0, "mw")
                tok.nofwd = True
                prog.add(VOp("gmwrite", [Use(vec)], out=tok, dsts=[Mat(side.name, r0)], unit="mwrite", after=side.write_after()))
                toks.append(tok)
            side.writers = toks
            side.readers = []
        # --- vector products for every row group
        last_h = h == halves[-1]
        current_plain = None
        for gi, (chunk, live) in enumerate(groups):
            if x_direct:
                hpart = sorted({_vector_position(xop, xk, k)[2] for k in range(K)})[h]
                xv = bf(Mem(xop.space, 2, tuple((xa + hpart) * 2 for xa, _ in chunk)))
            else:
                fb = chunk[0][0][0]
                if current_plain != (h, fb):
                    plain_rows(xop, xk, xfree, h, fb)
                    current_plain = (h, fb)
                c0 = chunk[0][0][1]
                xv = bf(Use(read_columns(c0)))
            daddrs = [d[blocks.index(m)] for _, d in chunk]
            dsts = []
            if last_h:
                mask = None if live == 4 else Mask(pattern="1" * live + "0" * (4 - live))
                dsts = [Mem(out.space, 2, tuple(a * 2 for a in daddrs), mask=mask)]
            res = None if last_h else Value(2)
            prev = acc.get((m, gi))
            if prev is None:
                vop = VOp("gmmul", [Mat(side.name), Use(xv)], out=res, dsts=dsts, unit="mau", after=side.read_after())
            else:
                vop = VOp("gmfma", [Mat(side.name), Use(xv), Use(prev)], out=res, dsts=dsts, unit="mau", after=side.read_after())
            prog.add(vop)
            if res is not None:
                acc[(m, gi)] = res
            side.readers.append(vop.out or _token_for(prog, vop))
    return prog


# ---------------------------------------------------------------- half-precision 16x16 with a transposed vector operand

def _hm_slot(spec, axis, value):
    """Position of an index in a half-precision MAB vector (4 halves per PE: 2 long words x 2 lanes)
    and the long word offset inside the pair."""
    pe, lane, a = _vector_position(spec, axis, value)
    return 4 * pe + 2 * a + lane, a


def _gen_ht(cn, out, mop, xop, mk, xk, mfree, xfree, f_vec, f_addr, BF_OP="hbfe/9"):
    """K = 16 on the half matrix unit when one operand has its contracted axis on addresses.
    Rows of such an operand are written to the y side as plain halves and read back transposed
    (two columns per cycle). The matrix (x side) is written block-floated either from the direct
    operand's vectors or from the transposed columns (two rows per cycle); the vectors are either
    the direct operand's vectors or the transposed columns. Vector positions may be any
    permutation of the 16 halves of a MAB as long as all operands agree."""
    from .machine import Mask

    prog = VProgram()
    m_direct, x_direct = _is_vec(mop, mk), _is_vec(xop, xk)
    if m_direct == x_direct:
        raise CompileError("hm-t: exactly one operand is transposed")
    if not ((m_direct or (_is_addr(mop, mk) and _is_vec(mop, mfree))) and (x_direct or (_is_addr(xop, xk) and _is_vec(xop, xfree))) and _is_vec(out, f_vec)):
        raise CompileError("hm-t: axes are not on PE/lanes and addresses as needed")

    def pos_map(spec, ax):
        m = {}
        for k in range(spec.shape[ax]):
            p, a = _hm_slot(spec, ax, k)
            if a not in (0, 1) or p in m.values():
                raise CompileError("hm-t: an axis is not laid out as a half vector")
            m[k] = p
        return m

    kpos = pos_map(mop, mk) if m_direct else pos_map(xop, xk)
    opos = pos_map(out, f_vec)
    if m_direct:
        if any(kpos[k] != p for k, p in pos_map(mop, mk).items()):
            raise CompileError("hm-t: contracted positions differ")
    else:
        if pos_map(mop, mfree) != opos:
            raise CompileError("hm-t: matrix rows would need a permutation")
    if not x_direct:
        xfpos = pos_map(xop, xfree)
    if len(kpos) != 16:
        raise CompileError("hm-t: contraction length")

    def addr(spec, vals):
        idx = [0] * len(spec.shape)
        for a_, v in vals.items():
            idx[a_] = v
        a0, _, _ = _addr_of(spec, tuple(idx))
        return a0

    def pair(spec, vals, vec_axis):
        a0 = addr(spec, {**vals, vec_axis: 0})
        a0 -= _hm_slot(spec, vec_axis, 0)[1]
        if a0 % 2:
            raise CompileError("hm-t: a vector pair is not aligned")
        return a0

    k_at = {p: k for k, p in kpos.items()}
    # y side: the transposed operand's rows, row = position of the contracted index
    t_op, t_k, t_free = (xop, xk, xfree) if m_direct else (mop, mk, mfree)
    writers_y = []
    for t0 in range(0, 16, 4):
        src = Mem(t_op.space, 4, tuple(2 * pair(t_op, {t_k: k_at[t0 + c]}, t_free) for c in range(4)), rnd=True)
        tok = Value(0, "mw")
        tok.nofwd = True
        prog.add(VOp("hmwrite", [src], out=tok, dsts=[Mat("y", t0)], unit="mwrite"))
        writers_y.append(tok)
    reads = []  # (first column, block-floated transposed columns)
    for c0 in range(0, 16, 8):
        rd = VOp("hmread", [Mat("y", c0, 4)], out=Value(4), unit="mread", after=list(writers_y))
        prog.add(rd)
        bf = VOp(BF_OP, [Use(rd.out)], out=Value(4), unit="alu")
        prog.add(bf)
        reads.append((c0, bf.out))
    # x side: the matrix
    writers_x = []
    if m_direct:
        j_at = {p: j for j, p in opos.items()}
        for r0 in range(0, 16, 4):
            rows = [j_at.get(r0 + c) for c in range(4)]
            if any(j is None for j in rows):
                raise CompileError("hm-t: output does not fill the matrix rows")
            src = Mem(mop.space, 4, tuple(2 * pair(mop, {mfree: j}, mk) for j in rows), rnd=True)
            bf = VOp(BF_OP, [src], out=Value(2), unit="alu")
            prog.add(bf)
            tok = Value(0, "mw")
            tok.nofwd = True
            prog.add(VOp("hmwrite", [Use(bf.out)], out=tok, dsts=[Mat("x", r0)], unit="mwrite"))
            writers_x.append(tok)
    else:
        for c0, cols in reads:
            tok = Value(0, "mw")
            tok.nofwd = True
            prog.add(VOp("hmwrite", [Use(cols)], out=tok, dsts=[Mat("x", c0, 4)], unit="mwrite", after=list(writers_y)))
            writers_x.append(tok)
    # vectors and products
    n_out = out.shape[f_addr]
    if x_direct:
        items = list(range(n_out))
        for g0 in range(0, n_out, 4):
            grp = items[g0:g0 + 4]
            live = len(grp)
            grp = grp + [grp[-1]] * (4 - live)
            src = Mem(xop.space, 4, tuple(2 * pair(xop, {xfree: i}, xk) for i in grp), rnd=True)
            bf = VOp(BF_OP, [src], out=Value(2), unit="alu")
            prog.add(bf)
            outs = [pair(out, {f_addr: i}, f_vec) for i in grp]
            mask = None if live == 4 else Mask(pattern="1" * live + "0" * (4 - live), ll=True)
            prog.add(VOp("hmmul", [Mat("x"), Use(bf.out)], dsts=[Mem(out.space, 4, tuple(2 * a for a in outs), mask=mask)], unit="mau", after=list(writers_x)))
    else:
        f_at = {p: f for f, p in xfpos.items()}
        for c0, cols in reads:
            for word, off in ((0, 0), (2, 1)):
                cs = [c0 + 2 * c + off for c in range(4)]
                fs = [f_at.get(c) for c in cs]
                live = [f for f in fs if f is not None and f < n_out]
                if not live:
                    continue
                if len(live) != 4:
                    raise CompileError("hm-t: partial column groups")
                outs = [pair(out, {f_addr: f}, f_vec) for f in fs]
                prog.add(VOp("hmmul", [Mat("x"), Use(cols, wl=2, word=word)], dsts=[Mem(out.space, 4, tuple(2 * a for a in outs))], unit="mau", after=list(writers_x)))
    return prog
