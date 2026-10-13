"""q11_polytope_independent.py -- member-side INDEPENDENT exact vertex enumeration.

Object (owner-indexed, 0-based; see members/dirichlet-cut-audit-cc2/Q11-ANCHOR-CHORD-DOMAIN.md):
  q = 11 owners 0..10 in owned-arc cyclic order; d_j = L - theta_j, L = 2 asin U,
  Delta = 11L - 2pi, box 0 <= d_j <= L, and for every chord middle label i the cut
      d_{(i-1)%11} + d_i + d_{(i+1)%11} >= G,   G = 3L - 2 asin(2U) = 3L - B.
Canonical cases: middles [] (no chord), [1] (one chord), [1,3] (two chords, shared label 2).

Independence: no import of any lead kernel/helper.
  * constants are recomputed here (Machin arctan series for pi; positive-term asin series with a
    geometric tail), giving rational enclosures of L, B, 2pi;
  * every polytope coefficient is an exact Q^3 triple (cL, cB, cP) meaning cL*L + cB*B + cP*(2pi);
    all linear algebra is exact Fraction arithmetic;
  * vertex sets are computed by TWO different algorithms that must agree exactly:
      route A -- enumerate every independent 10-subset of the active constraints of the three
                 families (box zeros, box L-caps, cuts) and solve the (equality + 10 rows) system;
                 complete because every vertex is the unique solution of some independent
                 10-subset of its active constraints, and two simultaneously active L-caps are
                 infeasible since 2L > Delta;
      route B -- recursive hyperplane cutting: new vertices of P ∩ H are exactly the crossings of H
                 with edges of P (a vertex of P ∩ H cannot lie in the relative interior of a face
                 of dimension >= 2), edges recomputed each stage by an exact rank test;
  * every comparison is decided by rigorous interval evaluation of the triples; equality of
    coordinates is exact triple equality.
Found while building this (recorded because it is a real trap): the crossing of a cut with an
edge must be computed by SOLVING the rational active system, not by interpolating between the two
edge values.  The crossing point is a rational combination of (L,B,2pi), but the interpolation
scalar is a ratio of two module elements and is generically irrational.

Coverage audit (exact unless marked provisional):
  * every enumerated vertex is feasible, and its active constraints plus the equality have full
    rank 11 (so it is a genuine 0-dimensional face);
  * active-constraint distribution, the vertex-constraint incidence identity, the degree
    distribution from the rank-based edge test, and the graph identity sum(deg) = 2E;
  * the D_11 edge count is cross-checked against the hand-derived combinatorial edge list
    (V(k,j) ~ V(k,j') same cap index, and V(k,j) ~ V(j,k)): 11*45 + 55 = 550;
  * provisional (clearly labelled): facet detection by evaluating tight sets at two different
    rational surrogates inside the certified boxes -- this is proposal-level, since the real
    affine dimension is not decidable from the symbolic triples alone.
"""

from fractions import Fraction as F
from itertools import combinations
import json
import math
import os
import sys

sys.set_int_max_str_digits(200000)

U = F("0.33173203427623414")          # threshold used by the lead (exact as written)
Q = 11


# ----------------------------------------------------------------------------- constants
def arctan_inv_bounds(m, n):
    """[lo, hi] for atan(1/m), m integer > 0, alternating series with decreasing terms."""
    s = F(0)
    for k in range(n):
        t = F(1, m ** (2 * k + 1) * (2 * k + 1))
        s += t if k % 2 == 0 else -t
    t_next = F(1, m ** (2 * n + 1) * (2 * n + 1))
    if n % 2 == 0:
        return s, s + t_next
    return s - t_next, s


def pi_bounds(n=40):
    a_lo, a_hi = arctan_inv_bounds(5, n)
    b_lo, b_hi = arctan_inv_bounds(239, n)
    return 16 * a_lo - 4 * b_hi, 16 * a_hi - 4 * b_lo


def asin_bounds(x, n=100):
    """[lo, hi] for asin(x), 0 < x < 1: positive terms with c_k <= 1 tail bound."""
    s = F(0)
    for k in range(n):
        c = F(math.comb(2 * k, k), 4 ** k * (2 * k + 1))
        s += c * x ** (2 * k + 1)
    tail = x ** (2 * n + 1) / (1 - x * x)
    return s, s + tail


PI_LO, PI_HI = pi_bounds()
T_LO, T_HI = 2 * PI_LO, 2 * PI_HI
_a, _b = asin_bounds(U)
A_LO, A_HI = _a, _b
L_LO, L_HI = 2 * _a, 2 * _b
_c, _d = asin_bounds(2 * U)
B_LO, B_HI = 2 * _c, 2 * _d
BOUNDS = ((L_LO, L_HI), (B_LO, B_HI), (T_LO, T_HI))

# ----------------------------------------------------------------------- triple arithmetic
ZERO = (F(0), F(0), F(0))


def tr(cL=0, cB=0, cP=0):
    return (F(cL), F(cB), F(cP))


def add(a, b):
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def mul(a, s):
    s = F(s)
    return (a[0] * s, a[1] * s, a[2] * s)


def dot(n, d):
    r = ZERO
    for c, v in zip(n, d):
        if c:
            r = add(r, mul(v, c))
    return r


def interval(t):
    lo = hi = F(0)
    for coef, (blo, bhi) in zip(t, BOUNDS):
        if coef >= 0:
            lo += coef * blo
            hi += coef * bhi
        else:
            lo += coef * bhi
            hi += coef * blo
    return lo, hi


UNDECIDED = []


def sgn(t, tag=""):
    if t == ZERO:
        return 0
    lo, hi = interval(t)
    if lo > 0:
        return 1
    if hi < 0:
        return -1
    UNDECIDED.append((tag, str(lo)[:30], str(hi)[:30]))
    return None


def dec(t, digits=22):
    lo, hi = interval(t)
    return f"{float((lo + hi) / 2):.{digits}g}"


LTR, BTR, DTR = tr(1, 0, 0), tr(0, 1, 0), tr(0, 0, 1)
DELTA = tr(11, 0, -1)          # 11L - 2pi
GTR = tr(3, -1, 0)             # G = 3L - B

CHAIN = []
for name, a, b in [
    ("9L < 2pi", tr(9, 0, 0), DTR),
    ("2pi < 10L", DTR, tr(10, 0, 0)),
    ("2L < B", tr(2, 0, 0), BTR),
    ("B < 3L", BTR, tr(3, 0, 0)),
    ("7L + B < 2pi", tr(7, 1, 0), DTR),
    ("2B + 5L < 2pi", tr(5, 2, 0), DTR),
    ("Delta < 2L (two active L-caps infeasible)", DELTA, tr(2, 0, 0)),
    ("Delta < 3L", DELTA, tr(3, 0, 0)),
    ("Delta - L < G", tr(10, 0, -1), GTR),
    ("G < L", GTR, LTR),
    ("Delta - G < L", sub(DELTA, GTR), LTR),
]:
    CHAIN.append({"inequality": name, "holds": sgn(sub(a, b), name) == -1})


def constraints(middles):
    """(normal:list[int], rhs:triple, label) meaning normal . d >= rhs."""
    cons = []
    for j in range(Q):
        n = [0] * Q
        n[j] = 1
        cons.append((n, ZERO, f"d{j}>=0"))
    for j in range(Q):
        n = [0] * Q
        n[j] = -1
        cons.append((n, mul(LTR, -1), f"d{j}<=L"))
    for i in middles:
        n = [0] * Q
        for m in ((i - 1) % Q, i, (i + 1) % Q):
            n[m] = 1
        cons.append((n, GTR, f"cut{i}"))
    return cons


# ------------------------------------------------------------------------- exact linear algebra
def invert(mat):
    n = len(mat)
    A = [[F(x) for x in row] + [F(1) if i == j else F(0) for j in range(n)] for i, row in enumerate(mat)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if A[r][col] != 0:
                piv = r
                break
        if piv is None:
            return None
        A[col], A[piv] = A[piv], A[col]
        pv = A[col][col]
        A[col] = [x / pv for x in A[col]]
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [x - f * y for x, y in zip(A[r], A[col])]
    return [row[n:] for row in A]


def rank_int(rows):
    if not rows:
        return 0
    M = [[F(x) for x in row] for row in rows]
    rk = 0
    for col in range(len(M[0])):
        piv = None
        for r in range(rk, len(M)):
            if M[r][col] != 0:
                piv = r
                break
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        pv = M[rk][col]
        M[rk] = [x / pv for x in M[rk]]
        for r in range(len(M)):
            if r != rk and M[r][col] != 0:
                f = M[r][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[rk])]
        rk += 1
        if rk == len(M):
            break
    return rk


def solve_system(rows, rhs):
    """square system rows . d = rhs with rows integer normals, rhs triples"""
    Minv = invert(rows)
    if Minv is None:
        return None
    d = []
    for i in range(Q):
        acc = ZERO
        for j in range(Q):
            if Minv[i][j]:
                acc = add(acc, mul(rhs[j], Minv[i][j]))
        d.append(acc)
    return d


EQ_ROW = [1] * Q


def feasible(d, cons):
    for n, rhs, lab in cons:
        s = sgn(sub(dot(n, d), rhs), lab)
        if s is None or s < 0:
            return False
    return True


def active_set(d, cons):
    return [k for k, (n, rhs, lab) in enumerate(cons) if sub(dot(n, d), rhs) == ZERO]


def adjacent(u, v, cons, Au, Av):
    common = [cons[k][0] for k in set(Au) & set(Av)]
    return rank_int([EQ_ROW] + common) == Q - 1


def edges_of(verts, cons):
    Av = [active_set(v, cons) for v in verts]
    E = []
    for a in range(len(verts)):
        for b in range(a + 1, len(verts)):
            if len(set(Av[a]) & set(Av[b])) >= Q - 2 and adjacent(verts[a], verts[b], cons, Av[a], Av[b]):
                E.append((a, b))
    return E, Av


# ------------------------------------------------------------------------- route A: basis
def route_basis(middles):
    cons = constraints(middles)
    nz = [k for k, c in enumerate(cons) if c[2].endswith(">=0")]
    nL = [k for k, c in enumerate(cons) if c[2].endswith("<=L")]
    nC = [k for k, c in enumerate(cons) if c[2].startswith("cut")]
    verts = set()
    tried = 0
    for ltake in (0, 1):                       # two active L-caps would need 2L <= Delta: impossible
        for lcomb in combinations(nL, ltake):
            for csize in range(0, len(nC) + 1):
                for ccomb in combinations(nC, csize):
                    zsize = 10 - ltake - csize
                    if zsize < 0 or zsize > len(nz):
                        continue
                    for zcomb in combinations(nz, zsize):
                        idx = list(lcomb) + list(ccomb) + list(zcomb)
                        tried += 1
                        rows = [EQ_ROW] + [cons[k][0] for k in idx]
                        rhs = [DELTA] + [cons[k][1] for k in idx]
                        if rank_int(rows) != Q:
                            continue
                        d = solve_system(rows, rhs)
                        if d is None:
                            continue
                        t = tuple(d)
                        if feasible(t, cons):
                            verts.add(t)
    return verts, tried


# ------------------------------------------- route B: recursive cutting + rank adjacency
def initial_vertices():
    verts = []
    for k in range(Q):
        for j in range(Q):
            if j == k:
                continue
            d = [ZERO] * Q
            d[k] = LTR
            d[j] = tr(10, 0, -1)               # Delta - L
            verts.append(tuple(d))
    return verts


def hand_edge_count():
    """combinatorial edge list of D_11: V(k,j) ~ V(k,j') (same cap index) and V(k,j) ~ V(j,k)"""
    idx = {(k, j): n for n, (k, j) in enumerate((k, j) for k in range(Q) for j in range(Q) if j != k)}
    E = set()
    for k in range(Q):
        js = [j for j in range(Q) if j != k]
        for a in range(len(js)):
            for b in range(a + 1, len(js)):
                E.add(frozenset((idx[(k, js[a])], idx[(k, js[b])])))
    for k in range(Q):
        for j in range(Q):
            if j != k:
                E.add(frozenset((idx[(k, j)], idx[(j, k)])))
    return idx, E


def crossing_point(u, v, cons, ci):
    """cut ci intersected with the line through the edge (u,v), by exact active-system solve"""
    Au, Av = active_set(u, cons), active_set(v, cons)
    rows = [EQ_ROW]
    rhs = [DELTA]
    cur = rank_int(rows)
    for k in sorted(set(Au) & set(Av)):
        cand = rows + [cons[k][0]]
        if rank_int(cand) > cur:
            rows, rhs, cur = cand, rhs + [cons[k][1]], cur + 1
        if cur == Q - 1:
            break
    if cur != Q - 1:
        return None
    rows = rows + [cons[ci][0]]
    rhs = rhs + [cons[ci][1]]
    if rank_int(rows) != Q:
        return None
    d = solve_system(rows, rhs)
    return None if d is None else tuple(d)


def route_cut(middles):
    allcons = constraints(middles)
    cuts = [c for c in allcons if c[2].startswith("cut")]
    cons = constraints([])
    verts = initial_vertices()
    stages = []
    for cut in cuts:
        idx = len(cons)
        consx = cons + [cut]
        E, _ = edges_of(verts, cons)
        keep, cross = [], []
        for v in verts:
            s = sgn(sub(dot(cut[0], v), cut[1]), cut[2])
            if s is None:
                raise RuntimeError("undecided sign " + cut[2])
            if s >= 0:
                keep.append(v)
        for (a, b) in E:
            u, v = verts[a], verts[b]
            au = sgn(sub(dot(cut[0], u), cut[1]), cut[2])
            av = sgn(sub(dot(cut[0], v), cut[1]), cut[2])
            if au is None or av is None:
                raise RuntimeError("undecided sign " + cut[2])
            if (au > 0 > av) or (av > 0 > au):
                pt = crossing_point(u, v, consx, idx)
                if pt is not None and feasible(pt, consx):
                    cross.append(pt)
        cons = consx
        seen, out = set(), []
        for d in keep + cross:
            if d in seen:
                continue
            seen.add(d)
            out.append(d)
        verts = [d for d in out if feasible(d, cons)]
        stages.append({"cut": cut[2], "vertices_before": len(keep) + len(set(cross)),
                       "kept": len(keep), "edge_crossings": len(set(cross)),
                       "vertices_after": len(verts)})
    return verts, stages


# ------------------------------------------------------------------------- coverage audit
def surrogate_facets(verts, cons, Ls, Bs, Ts):
    """PROVISIONAL: evaluate coordinates numerically at a rational surrogate inside the certified
    boxes and count constraints whose tight vertex set has real affine dimension 9."""
    def val(t):
        return t[0] * Ls + t[1] * Bs + t[2] * Ts
    acts = []
    for v in verts:
        a = []
        for k, (n, rhs, lab) in enumerate(cons):
            if sum(n[i] * val(v[i]) for i in range(Q)) == val(rhs):
                a.append(k)
        acts.append(a)
    facets, inc = [], 0
    for k, (n, rhs, lab) in enumerate(cons):
        tight = [v for v, a in zip(verts, acts) if k in a]
        if len(tight) < 2:
            continue
        base = tight[0]
        rows = [[val(v[i]) - val(base[i]) for i in range(Q)] for v in tight[1:]]
        dim = rank_int(rows)
        if dim == 9:
            facets.append(lab)
            inc += len(tight)
    return len(facets), inc


def audit(name, verts, cons, stages, tried):
    acts = [active_set(v, cons) for v in verts]
    ranks = [rank_int([EQ_ROW] + [cons[k][0] for k in a]) for a in acts]
    E, _ = edges_of(verts, cons)
    deg = [0] * len(verts)
    for a, b in E:
        deg[a] += 1
        deg[b] += 1
    # incidence identity: sum over constraints of |tight| == sum over vertices of |active|
    inc = 0
    for k in range(len(cons)):
        inc += sum(1 for a in acts if k in a)
    act_total = sum(len(a) for a in acts)
    # provisional facet probe at two different rational surrogates inside the certified boxes
    Ls1, Bs1, Ts1 = (L_LO + L_HI) / 2, (B_LO + B_HI) / 2, (T_LO + T_HI) / 2
    Ls2 = L_LO + (L_HI - L_LO) / 5
    Bs2 = B_LO + (B_HI - B_LO) / 7
    Ts2 = T_LO + (T_HI - T_LO) / 3
    f1, i1 = surrogate_facets(verts, cons, Ls1, Bs1, Ts1)
    f2, i2 = surrogate_facets(verts, cons, Ls2, Bs2, Ts2)
    return {
        "case": name,
        "vertices": len(verts),
        "edges": len(E),
        "basis_subsets_solved": tried,
        "active_counts": {c: sum(1 for a in acts if len(a) == c) for c in sorted(set(len(a) for a in acts))},
        "min_active_constraints": min(len(a) for a in acts),
        "max_active_constraints": max(len(a) for a in acts),
        "all_active_sets_full_rank": min(ranks) == Q,
        "all_vertices_feasible": all(feasible(v, cons) for v in verts),
        "degree_distribution": {d: deg.count(d) for d in sorted(set(deg))},
        "degree_sum_equals_2E": sum(deg) == 2 * len(E),
        "incidence_identity_holds": inc == act_total,
        "cut_stages": stages,
        "provisional_facet_probe": {"facets_surrogate1": f1, "facets_surrogate2": f2,
                                    "agree": f1 == f2,
                                    "incidence_surrogate": [i1, i2],
                                    "note": "proposal level only: real affine dimension of tight "
                                            "sets is evaluated at rational surrogates inside the "
                                            "certified boxes, not decided symbolically"},
        "vertices_owner_indexed_triples": [[[str(c) for c in v[j]] for j in range(Q)] for v in verts],
    }


# --------------------------------------------------------------------------------- main
def main():
    here = os.path.dirname(os.path.abspath(__file__))
    res = {
        "schema": "member-independent-q11-polytope/v1",
        "threshold_U": str(U),
        "certified_constant_bounds": {
            "L=2asinU": [str(L_LO), str(L_HI)],
            "B=2asin2U": [str(B_LO), str(B_HI)],
            "2pi": [str(T_LO), str(T_HI)],
        },
        "display_only_midpoints": {
            "L": dec(LTR), "B": dec(BTR), "2pi": dec(DTR),
            "Delta=11L-2pi": dec(DELTA), "Delta-L": dec(tr(10, 0, -1)), "G=3L-B": dec(GTR),
            "asinU": dec(tr(0, 0, 0) if False else (F(0), F(0), F(0))),
        },
        "certified_chains": CHAIN,
        "hand_edge_count_D11": len(hand_edge_count()[1]),
        "cases": {},
        "undecided_signs": [],
    }
    res["display_only_midpoints"]["asinU"] = f"{float((A_LO + A_HI) / 2):.22g}"
    for name, middles in [("no_chord", []), ("one_chord_middle1", [1]), ("two_chords_middles1_3", [1, 3])]:
        va, tried = route_basis(middles)
        vb, stages = route_cut(middles)
        agree = va == set(vb)
        assert agree, (name, len(va), len(vb))
        verts = sorted(va)
        aud = audit(name, verts, cons=constraints(middles), stages=stages, tried=tried)
        aud["routes_agree_exactly"] = True
        res["cases"][name] = aud
    # D_11 edge cross-check: rank-based edges == hand-derived combinatorial edges
    cons0 = constraints([])
    V0 = initial_vertices()
    E0, _ = edges_of(V0, cons0)
    idx, Ehand = hand_edge_count()
    rank_edges = {frozenset(e) for e in E0}
    res["D11_edge_crosscheck"] = {
        "rank_based_edges": len(rank_edges),
        "hand_derived_edges": len(Ehand),
        "sets_identical": rank_edges == Ehand,
    }
    res["undecided_signs"] = UNDECIDED
    with open(os.path.join(here, "q11-polytope-independent.json"), "w") as fh:
        json.dump(res, fh, indent=1)
    for name, a in res["cases"].items():
        print(f"{name:26s} V={a['vertices']:4d} E={a['edges']:4d} active={a['active_counts']} "
              f"deg={a['degree_distribution']} fullrank={a['all_active_sets_full_rank']} "
              f"incid={a['incidence_identity_holds']} stages={[(s['kept'], s['edge_crossings'], s['vertices_after']) for s in a['cut_stages']]} "
              f"facets={a['provisional_facet_probe']['facets_surrogate1']}/{a['provisional_facet_probe']['facets_surrogate2']}")
    print("D11 edge crosscheck:", res["D11_edge_crosscheck"])
    print("chains:", [(c["inequality"], c["holds"]) for c in CHAIN])
    print("undecided:", len(UNDECIDED), "display:", res["display_only_midpoints"])


if __name__ == "__main__":
    main()
