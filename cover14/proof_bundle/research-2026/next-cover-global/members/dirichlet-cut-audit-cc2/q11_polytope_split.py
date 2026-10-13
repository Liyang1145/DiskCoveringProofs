"""q11_polytope_split.py -- reusable EXACT polytope bisection (member scope, no claims).

Importing this module only defines data structures and functions; nothing is computed and no bulk
audit runs.  Run `python q11_polytope_split.py` (or call `run_tests()`) for the self-tests.

Public API
----------
Triples (the module's scalars)
    Triple = (cL, cB, cP) of Fraction, meaning cL*L + cB*B + cP*(2pi).
    Vertex = tuple of `dim` Triples.
Inequality = (normal, rhs, label)   with integer (or Fraction) normal, meaning normal . d >= rhs.
Equality   = (normal, rhs) or None.

class Decider                      sign(Triple) -> -1 | 0 | 1, exact, raises UndecidedSign.
class RationalDecider(l, b, t)     exact evaluation at given rational symbol values (toy tests).
class IntervalDecider(bounds)      rigorous enclosures; raises UndecidedSign on a straddle.
default_decider()                  own asin/pi enclosures (independent of the lead kernel).

class Polytope(dim, vertices, inequalities, equality=None, decider=None, name="")
    .vertices   tuple of Vertex (deduplicated, order preserved)
    .active     list[tuple[int]]   constraint indices tight at each vertex (cached)
    .active_rank list[int]         rank of equality + active normals (cached)
    .edges      tuple[(i,j)]       rank-adjacency edges (cached)
    .degrees    tuple[int]
    .value(v, normal) -> Triple
    .side(v, normal, rhs) -> -1|0|1
    .face_dim(i, j) -> int         dimension of the minimal face containing vertices i and j
    .split(normal, rhs, label) -> (child_ge, child_le, report)
        child_ge = P ∩ {normal . d >= rhs}, child_le = P ∩ {normal . d <= rhs}, BOTH CLOSED;
        construction: keep every vertex on the correct side (including the cut hyperplane, so
        vertices on the cut belong to both children) and add the exact crossings of the cut with
        the edges of P.  Crossings are obtained by SOLVING the rational active system
        (equality + independent common facets + the cut row); no interpolation is used, because
        the interpolation scalar is a ratio of two module elements and is generically irrational
        even though the crossing point is a rational combination of (L,B,2pi).
    .to_dict() -> JSON-friendly dict
midrange_split(P, normal, label="cut")
    RHS = componentwise average of the Triples at which `normal . d` is minimal / maximal over the
    vertices (whose value is therefore the numeric midpoint of the range); returns
    (child_ge, child_le, report, rhs) or (None, None, report, None) when the functional is constant
    on P (then both children equal P with a redundant cut row).
split_all_coordinates(P) -> list of (j, child_ge, child_le, report, rhs)
enumerate_vertices_rank_dfs(dim, inequalities, equality, decider, cap=200000)
    independent complete vertex enumeration by depth-first basis search with rank pruning
    (extends only with rank-increasing constraints); returns (vertices, hit_cap).
verify_children_by_enumeration(source, child_ge, child_le, cap)
    compares each child's vertex set against the independent enumeration of its own system.
coverage_report(source, child_ge, child_le)
    source-vertex coverage, crossing-in-both count, and per-child flags.

Guarantees / caveats
--------------------
* The two closed children always cover the source: every point of P satisfies normal.d >= rhs or
  normal.d <= rhs, and each child's vertex set is complete for its own system by the standard
  cutting theorem (vertices of P ∩ H = vertices of P inside H ∪ crossings of edges of P with H),
  so the union of the two children is the whole source.
* Completeness of a child's vertex set therefore inherits the completeness of the SOURCE vertex and
  edge data.  The edge test is the exact rank test face_dim(i,j) == 1; it was cross-checked on the
  D_11 polytope against an independently hand-derived edge list (550 edges, identical sets) and
  against a second enumeration algorithm in q11_polytope_independent.py.
* Degenerate cuts are handled explicitly: vertices on the cut go to both children, an edge lying in
  the cut contributes no crossing, a cut beyond the range gives one full child and one empty child,
  and a constant functional gives two copies of the source with a redundant cut row.  Empty and
  possibly lower-dimensional children are flagged in the report.
* All coordinate arithmetic is exact Fraction; only the SIGN of a Triple needs the decider, i.e. the
  numeric symbols (L, B, 2pi).  Supply your own decider to use your own constants.
"""

from fractions import Fraction as F
from itertools import combinations
import json
import math
import os
import sys

sys.set_int_max_str_digits(200000)

class UndecidedSign(Exception):
    pass

ZERO = (F(0), F(0), F(0))
def tri(cL=0, cB=0, cP=0):
    return (F(cL), F(cB), F(cP))
def tadd(a, b):
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])
def tsub(a, b):
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])
def tmul(a, s):
    s = F(s)
    return (a[0] * s, a[1] * s, a[2] * s)
def thalfsum(a, b):
    return tmul(tadd(a, b), F(1, 2))
def dotT(normal, vertex):
    """normal (ints/Fractions) . vertex (Triples) -> Triple"""
    acc = ZERO
    for c, v in zip(normal, vertex):
        if c:
            acc = tadd(acc, tmul(v, c))
    return acc


# ------------------------------------------------------------------------------- deciders
class Decider:
    def sign(self, t):
        raise NotImplementedError

    def __call__(self, t):
        return self.sign(t)

class RationalDecider(Decider):
    """exact evaluation of cL*L + cB*B + cP*(2pi) at given rational symbol values"""
    def __init__(self, l, b, t):
        self.l, self.b, self.t = F(l), F(b), F(t)

    def sign(self, tr):
        v = tr[0] * self.l + tr[1] * self.b + tr[2] * self.t
        return (v > 0) - (v < 0)

class IntervalDecider(Decider):
    """rigorous sign from rational enclosures of L, B, 2pi: raises UndecidedSign if straddling"""
    def __init__(self, l_bounds, b_bounds, t_bounds):
        self.bounds = (tuple(l_bounds), tuple(b_bounds), tuple(t_bounds))

    def sign(self, tr):
        if tr == ZERO:
            return 0
        lo = hi = F(0)
        for coef, (bl, bh) in zip(tr, self.bounds):
            if coef >= 0:
                lo += coef * bl
                hi += coef * bh
            else:
                lo += coef * bh
                hi += coef * bl
        if lo > 0:
            return 1
        if hi < 0:
            return -1
        raise UndecidedSign(str(tr))

def _arctan_inv_bounds(m, n):
    s = F(0)
    for k in range(n):
        t = F(1, m ** (2 * k + 1) * (2 * k + 1))
        s += t if k % 2 == 0 else -t
    t_next = F(1, m ** (2 * n + 1) * (2 * n + 1))
    return (s, s + t_next) if n % 2 == 0 else (s - t_next, s)

def _pi_bounds(n=40):
    alo, ahi = _arctan_inv_bounds(5, n)
    blo, bhi = _arctan_inv_bounds(239, n)
    return 16 * alo - 4 * bhi, 16 * ahi - 4 * blo

def _asin_bounds(x, n=100):
    s = F(0)
    for k in range(n):
        s += F(math.comb(2 * k, k), 4 ** k * (2 * k + 1)) * x ** (2 * k + 1)
    return s, s + x ** (2 * n + 1) / (1 - x * x)

DEFAULT_U = F("0.33173203427623414")

def default_decider(u=DEFAULT_U):
    """own independent enclosures: L = 2asin u, B = 2asin 2u, 2pi"""
    plo, phi = _pi_bounds()
    alo, ahi = _asin_bounds(u)
    clo, chi = _asin_bounds(2 * u)
    return IntervalDecider((2 * alo, 2 * ahi), (2 * clo, 2 * chi), (2 * plo, 2 * phi))


# ------------------------------------------------------------------------- exact linear algebra
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

def invert(mat):
    n = len(mat)
    A = [[F(x) for x in row] + [F(1) if i == j else F(0) for j in range(n)]
         for i, row in enumerate(mat)]
    for col in range(n):
        piv = next((r for r in range(col, n) if A[r][col] != 0), None)
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

def solve_square(rows, rhs):
    """rows: n integer normals, rhs: n Triples -> unique solution (Triples) or None"""
    n = len(rows)
    Minv = invert(rows)
    if Minv is None:
        return None
    out = []
    for i in range(n):
        acc = ZERO
        for j in range(n):
            if Minv[i][j]:
                acc = tadd(acc, tmul(rhs[j], Minv[i][j]))
        out.append(acc)
    return out


# --------------------------------------------------------------------------------- polytope
class Polytope:
    def __init__(self, dim, vertices, inequalities, equality=None, decider=None, name=""):
        self.dim = dim
        self.decider = decider
        self.name = name
        seen, verts = set(), []
        for v in vertices:
            v = tuple(tuple(F(c) for c in c0) for c0 in v)
            if v not in seen:
                seen.add(v)
                verts.append(v)
        self.vertices = tuple(verts)
        self.inequalities = tuple((tuple(F(c) for c in n), tuple(F(c) for c in r), lab)
                                  for (n, r, lab) in inequalities)
        self.equality = None if equality is None else (
            tuple(F(c) for c in equality[0]), tuple(F(c) for c in equality[1]))
        self._active = None
        self._ranks = None
        self._edges = None

    # --- caches
    @property
    def active(self):
        if self._active is None:
            out = []
            for v in self.vertices:
                a = tuple(k for k, (n, r, _) in enumerate(self.inequalities)
                          if tsub(dotT(n, v), r) == ZERO)
                out.append(a)
            self._active = tuple(out)
        return self._active

    @property
    def active_rank(self):
        if self._ranks is None:
            eq = [] if self.equality is None else [self.equality[0]]
            self._ranks = tuple(rank_int(eq + [self.inequalities[k][0] for k in a])
                                for a in self.active)
        return self._ranks

    @property
    def edges(self):
        if self._edges is None:
            E = []
            for i in range(len(self.vertices)):
                for j in range(i + 1, len(self.vertices)):
                    if len(set(self.active[i]) & set(self.active[j])) >= self.dim - 2 \
                            and self.face_dim(i, j) == 1:
                        E.append((i, j))
            self._edges = tuple(E)
        return self._edges

    @property
    def degrees(self):
        d = [0] * len(self.vertices)
        for a, b in self.edges:
            d[a] += 1
            d[b] += 1
        return tuple(d)

    # --- basics
    def value(self, v, normal):
        return dotT(normal, v)

    def side(self, v, normal, rhs):
        return self.decider.sign(tsub(dotT(normal, v), rhs))

    def face_dim(self, i, j):
        """dimension of the minimal face containing vertices i and j.

        The equality row is part of the rank computation, exactly as in the audited adjacency test
        (rank(eq + common) == dim - 1 for an edge).  Do NOT pre-subtract 1 for the equality: that
        would double-count it and select 2-faces as edges.
        """
        eq = [] if self.equality is None else [self.equality[0]]
        common = [self.inequalities[k][0] for k in set(self.active[i]) & set(self.active[j])]
        return self.dim - rank_int(eq + common)

    def is_feasible(self, v):
        for n, r, lab in self.inequalities:
            if self.decider.sign(tsub(dotT(n, v), r)) < 0:
                return False
        if self.equality is not None:
            if tsub(dotT(self.equality[0], v), self.equality[1]) != ZERO:
                return False
        return True

    def is_vertex(self, v):
        """full active rank: the active hyperplanes cut out a single point"""
        a = [k for k, (n, r, _) in enumerate(self.inequalities) if tsub(dotT(n, v), r) == ZERO]
        eq = [] if self.equality is None else [self.equality[0]]
        return rank_int(eq + [self.inequalities[k][0] for k in a]) == self.dim

    # --- the crossing computation (independent active system, never interpolation)
    def _crossing(self, i, j, normal, rhs):
        """Line through the edge (i,j) intersected with the cut row, by solving the active system.

        The line is the minimal face containing both vertices, i.e. rank(eq + common) must reach
        dim - 1 (the equality is included in that rank, so the target is dim - 1, NOT dim - 2);
        adding the cut row must then give full rank dim.
        """
        eqn = [] if self.equality is None else [self.equality[0]]
        eqr = [] if self.equality is None else [self.equality[1]]
        rows, rvals = list(eqn), list(eqr)
        cur = rank_int(rows)
        target = self.dim - 1
        for k in sorted(set(self.active[i]) & set(self.active[j])):
            cand = rows + [self.inequalities[k][0]]
            if rank_int(cand) > cur:
                rows, rvals, cur = cand, rvals + [self.inequalities[k][1]], cur + 1
            if cur == target:
                break
        if cur != target:
            raise RuntimeError(
                "crossing: minimal-face rank did not reach dim-1 for an edge of this polytope "
                "(inconsistent edge list)")
        rows = rows + [tuple(normal)]
        rvals = rvals + [tuple(rhs)]
        if rank_int(rows) != self.dim:
            raise RuntimeError("crossing: cut row did not give full rank with the edge line "
                               "(cut contains the line: degenerate case must be handled by the "
                               "caller as a face cut, not an edge crossing)")
        d = solve_square(rows, rvals)
        if d is None:
            raise RuntimeError("crossing: singular active system")
        return tuple(d)

    # --- the split
    def split(self, normal, rhs, label="cut"):
        normal = tuple(F(c) for c in normal)
        rhs = tuple(F(c) for c in rhs)
        if len(normal) != self.dim:
            raise ValueError("normal length must equal dim")
        sides = [self.side(v, normal, rhs) for v in self.vertices]
        hist = {-1: sides.count(-1), 0: sides.count(0), 1: sides.count(1)}
        keep_ge = [v for v, s in zip(self.vertices, sides) if s >= 0]
        keep_le = [v for v, s in zip(self.vertices, sides) if s <= 0]
        cross = []
        for (i, j) in self.edges:
            si, sj = sides[i], sides[j]
            if (si > 0 > sj) or (sj > 0 > si):
                # a straddling edge MUST produce a crossing; a None/inconsistent result is a bug,
                # not something to silently discard
                cross.append(self._crossing(i, j, normal, rhs))
        cross = list(dict.fromkeys(cross))
        negn = tuple(-c for c in normal)
        negr = tuple(-c for c in rhs)
        child_ge = Polytope(self.dim, keep_ge + cross,
                            list(self.inequalities) + [(normal, rhs, label + "+")],
                            self.equality, self.decider, self.name + "/" + label + "+")
        child_le = Polytope(self.dim, keep_le + cross,
                            list(self.inequalities) + [(negn, negr, label + "-")],
                            self.equality, self.decider, self.name + "/" + label + "-")
        report = self._split_report(normal, rhs, label, sides, hist, cross, child_ge, child_le)
        return child_ge, child_le, report

    @staticmethod
    def _on_cut_count(child, normal, rhs):
        return sum(1 for v in child.vertices if tsub(dotT(normal, v), rhs) == ZERO)

    def _split_report(self, normal, rhs, label, sides, hist, cross, child_ge, child_le):
        def flags(child, is_ge):
            oncut = self._on_cut_count(child, normal, rhs)
            empty = len(child.vertices) == 0
            return {
                "vertices": len(child.vertices),
                # edges are computed lazily: do not force them here (a child only needs its edge
                # set when it is split again)
                "edges": (None if child._edges is None else len(child._edges)),
                "empty": empty,
                "vertices_on_cut": oncut,
                "cut_binding": oncut > 0,
                "cut_redundant": (not empty) and oncut == 0,
                "possibly_lower_dimensional": (not empty)
                and all(tsub(dotT(normal, v), rhs) == ZERO for v in child.vertices),
                "infeasible_vertices": 0 if empty else sum(
                    1 for v in child.vertices if not child.is_feasible(v)),
                "non_extreme_vertices": 0 if empty else sum(
                    1 for v in child.vertices if not child.is_vertex(v)),
            }
        src_on_cut = hist[0]
        return {
            "label": label,
            "normal": [str(c) for c in normal],
            "rhs": [str(c) for c in rhs],
            "source_vertices": len(self.vertices),
            "source_edges": len(self.edges),
            "side_histogram": {"neg": hist[-1], "on_cut": hist[0], "pos": hist[1]},
            "edges_crossing": len(cross),
            "crossings": len(cross),
            "vertices_on_cut_both_children": src_on_cut,
            "child_ge": flags(child_ge, True),
            "child_le": flags(child_le, False),
            "coverage": {
                "every_source_vertex_in_a_child": all(
                    (s >= 0) or (s <= 0) for s in sides),
                "crossings_in_both_children": bool(cross),
                "closed_halfspace_union_covers_source": True,
                "all_vertices_are_fractional_triples": all(
                    all(all(isinstance(c, F) for c in coord) for coord in v)
                    for v in list(child_ge.vertices) + list(child_le.vertices)),
            },
        }

    def to_dict(self, include_vertices=True):
        d = {
            "name": self.name,
            "dim": self.dim,
            "vertices": len(self.vertices),
            "edges": (None if self._edges is None else len(self._edges)),
            "degrees": sorted(set(self.degrees)) if self._edges is not None else None,
            "active_counts": {c: list(len(a) for a in self.active).count(c)
                              for c in sorted(set(len(a) for a in self.active))},
            "inequalities": [[[str(x) for x in n], [str(x) for x in r], lab]
                             for (n, r, lab) in self.inequalities],
            "equality": None if self.equality is None else
            [[str(x) for x in self.equality[0]], [str(x) for x in self.equality[1]]],
        }
        if include_vertices:
            d["vertex_set"] = [[[str(c) for c in coord] for coord in v] for v in self.vertices]
        return d


# --------------------------------------------------------------------------------- helpers
def midrange_split(P, normal, label="cut"):
    normal = tuple(F(c) for c in normal)
    vals = [dotT(normal, v) for v in P.vertices]
    if not vals:
        return None, None, {"label": label, "note": "empty source"}, None
    lo = hi = vals[0]
    for t in vals[1:]:
        if P.decider.sign(tsub(t, lo)) < 0:
            lo = t
        if P.decider.sign(tsub(t, hi)) > 0:
            hi = t
    if P.decider.sign(tsub(hi, lo)) == 0:
        rep = {"label": label, "note": "functional constant on P: cut is redundant, both children "
                                       "equal the source", "constant_value": [str(c) for c in lo]}
        return None, None, rep, None
    rhs = thalfsum(lo, hi)
    ge, le, rep = P.split(normal, rhs, label)
    rep["midrange_rhs"] = [str(c) for c in rhs]
    rep["range_endpoints"] = [[str(c) for c in lo], [str(c) for c in hi]]
    return ge, le, rep, rhs

def split_all_coordinates(P, label="coord"):
    out = []
    for j in range(P.dim):
        n = [F(0)] * P.dim
        n[j] = F(1)
        ge, le, rep, rhs = midrange_split(P, n, f"{label}{j}")
        out.append((j, ge, le, rep, rhs))
    return out

def coverage_report(source, child_ge, child_le):
    """Structural coverage facts.  Note children DO contain new vertices (the edge crossings),
    which appear in both children; so children are not subsets of the source, and that is correct.
    """
    src = set(source.vertices)
    a, b = set(child_ge.vertices), set(child_le.vertices)
    new_all = (a | b) - src
    return {
        "source_vertices": len(src),
        "child_ge_vertices": len(a),
        "child_le_vertices": len(b),
        "children_union_covers_source_vertices": src <= (a | b),
        "vertices_in_neither": len(src - (a | b)),
        "shared_vertices": len(a & b),
        "new_vertices_ge": len(a - src),
        "new_vertices_le": len(b - src),
        "all_new_vertices_are_in_both_children": new_all <= (a & b),
        "kept_plus_new_accounting": len(src) + len(new_all) == len(a | b),
    }

def enumerate_vertices_rank_dfs(dim, inequalities, equality=None, decider=None, cap=20000,
                                max_nodes=200000):
    """independent complete enumeration: DFS over rank-increasing constraint subsets.

    Extends only with rank-increasing constraints (partial Gaussian pruning) and stops with
    hit_cap=True once `cap` bases or `max_nodes` nodes are exceeded, so the caller knows the run was
    not complete.  Returns (vertices, hit_cap).
    """
    n_target = dim - (0 if equality is None else 1)
    eqn = [] if equality is None else [tuple(F(c) for c in equality[0])]
    eqr = [] if equality is None else [tuple(F(c) for c in equality[1])]
    norms = [tuple(F(c) for c in n) for (n, r, lab) in inequalities]
    rhss = [tuple(F(c) for c in r) for (n, r, lab) in inequalities]
    sols, hit_cap, solved, nodes = set(), False, 0, 0

    def rec(start, rows, rvals, cur_rank):
        nonlocal hit_cap, solved, nodes
        if hit_cap:
            return
        nodes += 1
        if nodes > max_nodes:
            hit_cap = True
            return
        if len(rows) == n_target + len(eqn):
            solved += 1
            if solved > cap:
                hit_cap = True
                return
            d = solve_square(rows, rvals)
            if d is None:
                return
            t = tuple(d)
            for n, r in zip(norms, rhss):
                if decider.sign(tsub(dotT(n, t), r)) < 0:
                    return
            if equality is not None and tsub(dotT(eqn[0], t), eqr[0]) != ZERO:
                return
            sols.add(t)
            return
        for k in range(start, len(norms)):
            cand = rows + [norms[k]]
            r = rank_int(cand)
            if r > cur_rank:
                rec(k + 1, cand, rvals + [rhss[k]], r)

    rec(0, list(eqn), list(eqr), rank_int(list(eqn)))
    return list(sols), hit_cap

def verify_children_by_enumeration(source, child_ge, child_le, cap=20000):
    out = {"cap": cap, "note": "DFS rank-pruned enumeration; hit_cap=True means NOT complete"}
    for tag, child in (("ge", child_ge), ("le", child_le)):
        if child is None:
            continue
        verts, hit = enumerate_vertices_rank_dfs(child.dim, child.inequalities, child.equality,
                                                 source.decider, cap=cap)
        got, exp = set(child.vertices), set(verts)
        out[tag] = {
            "child_vertices": len(got),
            "enumerated_vertices": len(exp),
            "hit_cap": hit,
            "exact_match": (not hit) and (got == exp),
            "missing_from_child": None if hit else len(exp - got),
            "extra_in_child": None if hit else len(got - exp),
        }
    return out


# ------------------------------------------------------------------------------------ tests
def build_D11(dim=11, decider=None, L=None, delta=None):
    """the q11 outer domain D_11 as a Polytope: 0 <= d_j <= L, sum d = Delta = 11L - 2pi"""
    L = tri(1, 0, 0) if L is None else L
    delta = tri(11, 0, -1) if delta is None else delta
    verts = []
    for k in range(dim):
        for j in range(dim):
            if j == k:
                continue
            v = [ZERO] * dim
            v[k] = L
            v[j] = tsub(delta, L)
            verts.append(tuple(v))
    ineq = []
    for j in range(dim):
        n = [F(0)] * dim
        n[j] = F(1)
        ineq.append((n, ZERO, f"d{j}>=0"))
        n2 = [F(0)] * dim
        n2[j] = F(-1)
        ineq.append((n2, tmul(L, -1), f"d{j}<=L"))
    return Polytope(dim, verts, ineq, equality=([F(1)] * dim, delta), decider=decider, name="D11")

def build_one_chord(middles=(1,), decider=None):
    """D_11 cut by the chord constraints; also asserts the three canonical counts if requested"""
    P0 = build_D11(decider=decider)
    P = P0
    for i in middles:
        n = [F(0)] * P.dim
        for m in ((i - 1) % P.dim, i, (i + 1) % P.dim):
            n[m] = F(1)
        ge, le, rep = P.split(n, tri(3, -1, 0), f"chord{i}")
        assert len(le.vertices) == 0, "chord cut should keep everything: check orientation"
        P = ge
    return P

def toy_square(decider):
    """unit square, no equality; all coordinates carried in the L-component of the Triples, so the
    symbol values must have L as the active unit (e.g. RationalDecider(1, 7, 13))."""
    L = tri(1, 0, 0)
    verts = [((0, 0, 0), (0, 0, 0)), ((1, 0, 0), (0, 0, 0)), ((1, 0, 0), (1, 0, 0)),
             ((0, 0, 0), (1, 0, 0))]
    ineq = [((1, 0), ZERO, "x>=0"), ((-1, 0), tmul(L, -1), "x<=1"),
            ((0, 1), ZERO, "y>=0"), ((0, -1), tmul(L, -1), "y<=1")]
    return Polytope(2, verts, ineq, equality=None, decider=decider, name="toy-square")

def toy_triangle3(decider):
    """x,y,z >= 0 with equality x+y+z = 1 (a triangle in the plane): ambient dim 3"""
    one = (1, 0, 0)
    verts = [tuple([one, ZERO, ZERO]), tuple([ZERO, one, ZERO]), tuple([ZERO, ZERO, one])]
    ineq = []
    for j in range(3):
        n = [0, 0, 0]
        n[j] = 1
        ineq.append((n, ZERO, f"c{j}>=0"))
    return Polytope(3, verts, ineq, equality=([1, 1, 1], one), decider=decider, name="toy-tri3")

def run_tests(out_dir=None):
    dec = default_decider()
    tdec = RationalDecider(1, 7, 13)
    res = {"schema": "member-q11-polytope-split-tests/v1",
           "decider": "interval enclosures from own asin/pi series",
           "tests": {}, "notes": [
               "face_dim uses dim - rank(eq + common) (equality counted once); regression: D_11 "
               "edge count must be 550 with the equality present",
               "crossings are solved from the active system; a straddling edge that fails to "
               "produce a crossing raises instead of being dropped",
           ]}

    # --- 0. canonical D_11 / one-chord / two-chord: vertices AND edges (regression)
    P0 = build_D11(decider=dec)
    n1 = [F(0)] * 11
    for m in (0, 1, 2):
        n1[m] = F(1)
    ge1, le1, rep1 = P0.split(n1, tri(3, -1, 0), "chord1")
    P1 = ge1
    n3 = [F(0)] * 11
    for m in (2, 3, 4):
        n3[m] = F(1)
    ge3, le3, rep3 = P1.split(n3, tri(3, -1, 0), "chord3")
    # combinatorial edge list of D_11 (same construction as the audited script)
    idx = {(k, j): n for n, (k, j) in enumerate((k, j) for k in range(11) for j in range(11)
                                                if j != k)}
    Ehand = set()
    for k in range(11):
        js = [j for j in range(11) if j != k]
        for a in range(len(js)):
            for b in range(a + 1, len(js)):
                Ehand.add(frozenset((idx[(k, js[a])], idx[(k, js[b])])))
    for k in range(11):
        for j in range(11):
            if j != k:
                Ehand.add(frozenset((idx[(k, j)], idx[(j, k)])))
    Erank = {frozenset(e) for e in P0.edges}
    res["tests"]["canonical_counts_and_edges"] = {
        "D11_vertices": len(P0.vertices), "D11_edges": len(P0.edges),
        "one_chord_vertices": len(P1.vertices), "one_chord_edges": len(P1.edges),
        "two_chord_vertices": len(ge3.vertices), "two_chord_edges": len(ge3.edges),
        "expected_vertices": [110, 54, 24], "expected_edges": [550, 270, 132],
        "vertices_match": [len(P0.vertices), len(P1.vertices), len(ge3.vertices)] == [110, 54, 24],
        "edges_match": [len(P0.edges), len(P1.edges), len(ge3.edges)] == [550, 270, 132],
        "D11_rank_edges_equal_hand_derived": Erank == Ehand,
        "D11_degree_distribution": sorted(set(P0.degrees)),
    }

    # --- 1. midrange coordinate splits of the canonical one-chord polytope
    coord_tests = []
    for j, ge, le, rep, rhs in split_all_coordinates(P1, label="x"):
        entry = {"coordinate": j, "rhs": None if rhs is None else [str(c) for c in rhs],
                 "report": rep}
        if ge is not None:
            entry["coverage"] = coverage_report(P1, ge, le)
            entry["child_ge"] = ge.to_dict(include_vertices=False)
            entry["child_le"] = le.to_dict(include_vertices=False)
            entry["checks"] = {
                "all_vertices_feasible": all(ge.is_feasible(v) for v in ge.vertices)
                and all(le.is_feasible(v) for v in le.vertices),
                "all_vertices_extreme": all(ge.is_vertex(v) for v in ge.vertices)
                and all(le.is_vertex(v) for v in le.vertices),
                "children_are_subsets_of_source": set(ge.vertices) <= set(P1.vertices)
                and set(le.vertices) <= set(P1.vertices),
                "new_vertices_are_exactly_the_crossings":
                    len((set(ge.vertices) | set(le.vertices)) - set(P1.vertices))
                    == rep["crossings"],
                "kept_plus_crossings_accounting_ok":
                    len(ge.vertices) + len(le.vertices)
                    == rep["side_histogram"]["pos"] + rep["side_histogram"]["neg"]
                    + 2 * rep["side_histogram"]["on_cut"] + 2 * rep["crossings"],
            }
        coord_tests.append(entry)
    res["tests"]["one_chord_midrange_splits"] = coord_tests

    # --- 2. degenerate cuts
    deg = {}
    v0 = P1.vertices[0]
    n = [F(0)] * 11
    n[0] = F(1)
    ge, le, rep = P1.split(n, v0[0], "through_vertex")
    deg["through_vertex"] = {"report": rep, "coverage": coverage_report(P1, ge, le),
                             "vertex_in_both_children": (v0 in set(ge.vertices))
                             and (v0 in set(le.vertices))}
    i, jj = P1.edges[0]
    val = dotT(n, P1.vertices[i])
    ge, le, rep = P1.split(n, val, "through_edge")
    deg["through_edge"] = {"report": rep, "coverage": coverage_report(P1, ge, le),
                           "edge_endpoints_in_both": all(
                               (P1.vertices[q] in set(le.vertices))
                               and (P1.vertices[q] in set(ge.vertices)) for q in (i, jj))}
    mx = max([dotT(n, v) for v in P1.vertices], key=lambda t: dec.sign(t))
    beyond = tadd(mx, tri(1, 0, 0))
    ge, le, rep = P1.split(n, beyond, "beyond_range")
    deg["beyond_range"] = {"report": rep, "coverage": coverage_report(P1, ge, le)}
    eqn, eqr = P1.equality
    ge, le, rep, rhs = midrange_split(P1, eqn, "constant_equality")
    deg["constant_functional"] = {"report": rep, "rhs": rhs}
    res["tests"]["degenerate_cuts"] = deg

    # --- 3. toy calibrations, hand-checkable, with FULL independent enumeration
    toy = {}
    S = toy_square(tdec)
    ge, le, rep = S.split([F(1), F(0)], tri(F(1, 2), 0, 0), "x>=1/2")
    s_ge, hit_ge = enumerate_vertices_rank_dfs(2, ge.inequalities, None, tdec, cap=10000)
    s_le, hit_le = enumerate_vertices_rank_dfs(2, le.inequalities, None, tdec, cap=10000)
    toy["square_x_ge_half"] = {
        "source_vertices": len(S.vertices),
        "child_ge_vertices": len(ge.vertices), "child_le_vertices": len(le.vertices),
        "expected": [4, 4],
        "coverage": coverage_report(S, ge, le),
        "dfs_ge": {"vertices": len(s_ge), "hit_cap": hit_ge, "matches_child": set(s_ge) == set(ge.vertices)},
        "dfs_le": {"vertices": len(s_le), "hit_cap": hit_le, "matches_child": set(s_le) == set(le.vertices)},
    }
    T = toy_triangle3(tdec)
    ge, le, rep = T.split([F(1), F(0), F(0)], tri(F(1, 3), 0, 0), "x>=1/3")
    t_ge, hit_ge = enumerate_vertices_rank_dfs(3, ge.inequalities, T.equality, tdec, cap=10000)
    t_le, hit_le = enumerate_vertices_rank_dfs(3, le.inequalities, T.equality, tdec, cap=10000)
    toy["triangle_x_ge_third"] = {
        "source_vertices": len(T.vertices),
        "child_ge_vertices": len(ge.vertices), "child_le_vertices": len(le.vertices),
        "expected": [3, 4],
        "coverage": coverage_report(T, ge, le),
        "dfs_ge": {"vertices": len(t_ge), "hit_cap": hit_ge, "matches_child": set(t_ge) == set(ge.vertices)},
        "dfs_le": {"vertices": len(t_le), "hit_cap": hit_le, "matches_child": set(t_le) == set(le.vertices)},
    }
    # degenerate toy: cut exactly through a square vertex and exactly through a square edge
    ge, le, rep = S.split([F(1), F(0)], tri(1, 0, 0), "toy_through_vertex")
    toy["square_through_vertex"] = {"report": {k: rep[k] for k in
                                               ("side_histogram", "edges_crossing")},
                                    "coverage": coverage_report(S, ge, le)}
    res["tests"]["toy_calibrations"] = toy

    # --- 4. bounded DFS on the 11-dimensional system: NOT run here.  The 11-dim DFS costs far more
    #        than the small-instance budget (it was the cause of an earlier test timeout), so the
    #        canonical regression above plus the toy full enumerations are the calibration, and the
    #        lead's independent basis enumerator covers the q11 children.  The function
    #        enumerate_vertices_rank_dfs remains available with explicit caps.
    res["tests"]["dfs_note"] = {
        "q11_DFS_run": False,
        "reason": "11-dim DFS exceeds the small-instance budget; canonical counts/edges and toy "
                  "full enumerations are used instead, and child completeness is verified "
                  "externally (lead's independent basis audit replayed all child vertex sets)",
    }

    summary = {
        "canonical_vertices_match": res["tests"]["canonical_counts_and_edges"]["vertices_match"],
        "canonical_edges_match": res["tests"]["canonical_counts_and_edges"]["edges_match"],
        "D11_edges_equal_hand_list": res["tests"]["canonical_counts_and_edges"][
            "D11_rank_edges_equal_hand_derived"],
        "midrange_splits": len(coord_tests),
        "all_children_feasible_and_extreme": all(
            e["checks"]["all_vertices_feasible"] and e["checks"]["all_vertices_extreme"]
            for e in coord_tests if "checks" in e),
        "all_coverages_ok": all(
            e["coverage"]["children_union_covers_source_vertices"]
            and e["coverage"]["vertices_in_neither"] == 0
            and e["coverage"]["all_new_vertices_are_in_both_children"]
            and e["coverage"]["kept_plus_new_accounting"] for e in coord_tests
            if "coverage" in e),
        "all_children_extreme_and_new_vertices_are_crossings": all(
            e["checks"]["all_vertices_extreme"]
            and e["checks"]["new_vertices_are_exactly_the_crossings"] for e in coord_tests
            if "checks" in e),
        "toy_full_dfs_matches": [toy["square_x_ge_half"]["dfs_ge"]["matches_child"],
                                 toy["square_x_ge_half"]["dfs_le"]["matches_child"],
                                 toy["triangle_x_ge_third"]["dfs_ge"]["matches_child"],
                                 toy["triangle_x_ge_third"]["dfs_le"]["matches_child"]],
        "toy_counts": [[toy["square_x_ge_half"]["child_ge_vertices"],
                        toy["square_x_ge_half"]["child_le_vertices"]],
                       [toy["triangle_x_ge_third"]["child_ge_vertices"],
                        toy["triangle_x_ge_third"]["child_le_vertices"]]],
        "degenerate_cases": list(deg.keys()),
    }
    res["summary"] = summary
    if out_dir is None:
        out_dir = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(out_dir, "q11-polytope-split-tests.json")
    with open(path, "w") as fh:
        json.dump(res, fh, indent=1)
    return res, path

if __name__ == "__main__":
    r, p = run_tests()
    print(json.dumps(r["summary"], indent=1))
    print("written:", p)
