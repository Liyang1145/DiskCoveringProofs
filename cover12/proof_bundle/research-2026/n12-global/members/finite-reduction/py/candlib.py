"""candlib.py -- n=12 global: finite candidate reduction for the covering radius of a
*configuration*, with NO general-position / contact-graph / distinctness hypothesis.

Objects
-------
D = {x in R^2 : |x| <= 1}  (closed unit disk)
C = {c_1,...,c_n} c D  finite, nonempty; repeats (coincident centers) and 0 in C allowed.
f_C(x) = min_i |x - c_i|
R(C)  = max_{x in D} f_C(x)      (covering radius of C on D)

Finite candidate set K(C)
-------------------------
(a) the fixed point (1,0);
(b) for every center with |c_i| > 0, its antipode -c_i/|c_i|;
(c) for every pair of DISTINCT positions, the two points of the perpendicular
    bisector of (c_i,c_j) cut by the unit circle;
(d) for every non-collinear triple of DISTINCT positions, the circumcenter,
    KEPT ONLY IF |x| <= 1.

Claim under test (theorem to be proved, not assumed here):
    R(C) = max_{x in K(C)} f_C(x),  i.e. some maximizer lies in K(C).

This module provides:
  * candidate_points(C)          -> list of records (kind, idx, x, inside_D)
  * R_cand(C)                    -> max of f_C over candidates that lie in D
  * R_cand_all(C)                -> same but without the inside-D filter (diagnostic)
  * R_ref(C, ...)                -> reference value by grid + projected pattern search
                                    (independent of the candidate list; used only as a
                                    numerical cross-check / falsification instrument)
  * classify_argmax(C, x)        -> which degeneracy class the maximizer shows

All numerics are float64 diagnostics: they can falsify, they cannot certify.
"""
from __future__ import annotations

import itertools
import math

import numpy as np

POS_TOL = 1e-12  # for "distinct positions"
INSIDE_TOL = 1e-12


# ----------------------------------------------------------------- primitives
def f_min(x, C):
    """f_C(x) = min_i |x - c_i|; x shape (2,), C shape (n,2)."""
    d = C - np.asarray(x, dtype=float)
    return float(np.sqrt((d * d).sum(axis=1)).min())


def nearest_set(x, C, tol=1e-12):
    """Indices i whose distance attains the min (within tol)."""
    d = np.sqrt(((C - np.asarray(x, dtype=float)) ** 2).sum(axis=1))
    m = d.min()
    return [int(i) for i in np.nonzero(d <= m + max(tol, 1e-12 * max(1.0, m)))[0]]


def distinct_positions(C, tol=POS_TOL):
    """Return (reps, groups): representatives of distinct positions and grouping."""
    C = np.asarray(C, dtype=float)
    reps, groups = [], []
    for i in range(len(C)):
        for r, g in zip(reps, groups):
            if np.hypot(*(C[i] - C[r])) <= tol:
                g.append(i)
                break
        else:
            reps.append(i)
            groups.append([i])
    return reps, groups


def antipode(c):
    n = float(np.hypot(c[0], c[1]))
    if n == 0.0:
        return None
    return np.array([-c[0] / n, -c[1] / n])


def bisector_circle(a, b):
    """Intersections of perp. bisector of (a,b) with unit circle.

    Bisector: {x : x.n = h}, n = b - a (!= 0), h = (|b|^2 - |a|^2)/2.
    Distance from origin to line: |h|/|n|; = |m.u| with m midpoint, < 1 whenever
    a != b and |a|,|b| <= 1 (see proof doc, Lemma 2: no tangency case exists).
    """
    n = np.asarray(b, float) - np.asarray(a, float)
    nn = float(n @ n)
    if nn == 0.0:
        return []
    h = (float(b @ b) - float(a @ a)) / 2.0
    q = h / nn                      # foot of perpendicular from origin
    foot = q * n
    t2 = 1.0 - float(foot @ foot)
    if t2 < 0.0:
        return []                   # cannot happen for a!=b, |a|,|b|<=1
    t = math.sqrt(t2)
    u = np.array([-n[1], n[0]]) / math.sqrt(nn)
    return [foot + t * u, foot - t * u]


def circumcenter(a, b, c):
    """Circumcenter of triangle (a,b,c); None if collinear (degenerate)."""
    a = np.asarray(a, float); b = np.asarray(b, float); c = np.asarray(c, float)
    det = 2.0 * ((b - a) @ np.array([-(c - a)[1], (c - a)[0]]))
    if abs(det) <= 1e-14 * max(1.0, abs(det)):   # collinear / numerically degenerate
        return None
    d1 = float(b @ b) - float(a @ a)
    d2 = float(c @ c) - float(a @ a)
    M = np.array([[2.0 * (b - a)[0], 2.0 * (b - a)[1]],
                  [2.0 * (c - a)[0], 2.0 * (c - a)[1]]])
    return np.linalg.solve(M, np.array([d1, d2]))


# --------------------------------------------------------------- candidates
def candidate_points(C, keep_outside=True):
    """Finite candidate list.  keep_outside: retain (d)-circumcenters outside D as
    diagnostics (they must NOT be used in R_cand)."""
    C = np.asarray(C, dtype=float)
    reps, groups = distinct_positions(C)
    out = []

    # (a) fixed boundary point
    out.append(dict(kind="a", idx=(), pos=np.array([1.0, 0.0]),
                    inside=True, note="fixed (1,0)"))

    # (b) antipodes of nonzero centers (per position, duplicates collapse)
    for i in reps:
        p = antipode(C[i])
        if p is not None:
            out.append(dict(kind="b", idx=(i,), pos=p, inside=True,
                            note="antipode"))

    # (c) pair bisector  ∩  unit circle  (2 points per distinct pair)
    for i, j in itertools.combinations(reps, 2):
        for t, p in enumerate(bisector_circle(C[i], C[j])):
            out.append(dict(kind="c", idx=(i, j), pos=p, inside=True,
                            note=f"bis∩circle#{t}"))

    # (d) circumcenters of non-collinear triples
    for i, j, k in itertools.combinations(reps, 3):
        p = circumcenter(C[i], C[j], C[k])
        if p is None:
            continue
        inside = float(p @ p) <= 1.0 + INSIDE_TOL
        rec = dict(kind="d", idx=(i, j, k), pos=p, inside=inside,
                   note="circumcenter" + ("" if inside else " (outside D, excluded)"))
        if inside or keep_outside:
            out.append(rec)
    return out


def R_cand(C, verbose=False):
    """max of f_C over candidates lying in D (the criteria under test)."""
    C = np.asarray(C, dtype=float)
    best, arg = -1.0, None
    for rec in candidate_points(C):
        if not rec["inside"]:
            continue
        v = f_min(rec["pos"], C)
        rec["val"] = v
        if v > best:
            best, arg = v, rec
    if verbose:
        print("  candidates: n=%d  R_cand=%.15f  argmax=%s idx=%s"
              % (len(candidate_points(C)), best, arg["kind"], arg["idx"]))
    return best, arg


def R_cand_all(C):
    """Diagnostic: same max but WITHOUT the inside-D filter (upper reading)."""
    C = np.asarray(C, dtype=float)
    best, arg = -1.0, None
    for rec in candidate_points(C):
        v = f_min(rec["pos"], C)
        if v > best:
            best, arg = v, rec
    return best, arg


def R_by_class(C, verbose=False):
    """Max of f over each candidate class separately (essentiality analysis)."""
    C = np.asarray(C, dtype=float)
    out = {}
    for rec in candidate_points(C):
        if not rec["inside"]:
            continue
        v = f_min(rec["pos"], C)
        k = rec["kind"]
        if k not in out or v > out[k][0]:
            out[k] = (v, rec)
    if verbose:
        for k in "abcd":
            if k in out:
                print(f"    class {k}: R_{k} = {out[k][0]:.15f}  idx={out[k][1]['idx']}")
            else:
                print(f"    class {k}: (no candidate)")
    return out


def sandwich(C, n_grid=2001, chunk=2_000_000, rng_seed=1):
    """Sound (up to float rounding) two-sided reading of R(C).

    lower : R_cand (attained, so <= R(C))
    upper : max over grid of f + h*sqrt(2)/2 + fp_slack  (valid because f is
            1-Lipschitz and the grid of spacing h covers D with radius h*sqrt(2)/2)
    plus a pseudo-random violation scan (uniform on D, chunked).
    Returns dict.
    """
    C = np.asarray(C, float)
    n = len(C)
    Rc, arg = R_cand(C)
    h = 2.0 / (n_grid - 1.0)
    P = _grid_points(n_grid)
    fg = fmin_grid(P, C)
    gmax = float(fg.max())
    lip = h * math.sqrt(2.0) / 2.0
    fp_slack = 1e-12
    rng = np.random.default_rng(rng_seed)
    rmax, count = -1.0, max(200_000, chunk)
    done = 0
    while done < count:
        m = min(chunk, count - done)
        r = np.sqrt(rng.random(m))
        a = 2 * np.pi * rng.random(m)
        Q = np.stack([r * np.cos(a), r * np.sin(a)], axis=1)
        rmax = max(rmax, float(fmin_grid(Q, C).max()))
        done += m
    return dict(R_cand=Rc, R_cand_arg=arg, grid_max=gmax, lip=lip,
                upper=gmax + lip + fp_slack, lower=Rc,
                width=(gmax + lip + fp_slack) - Rc,
                violation_grid=gmax - Rc, violation_random=rmax - Rc,
                n_random=count)


# ------------------------------------------------- reference maximization
def _grid_points(n):
    ax = np.linspace(-1.0, 1.0, n)
    X, Y = np.meshgrid(ax, ax, indexing="ij")
    m = X * X + Y * Y <= 1.0
    return np.stack([X[m], Y[m]], axis=1)


def fmin_grid(P, C):
    """min_i |P - c_i| for all rows of P (streamed over centers)."""
    P = np.asarray(P, float)
    best = np.full(len(P), np.inf)
    for c in np.asarray(C, float):
        d = P - c
        np.minimum(best, np.sqrt((d * d).sum(axis=1)), out=best)
    return best


_DIRS = None


def _dirs():
    global _DIRS
    if _DIRS is None:
        ang = np.linspace(0.0, 2.0 * np.pi, 9)[:-1]
        _DIRS = np.stack([np.cos(ang), np.sin(ang)], axis=1)
    return _DIRS


def pattern_search(x0, C, step0=0.05, tol=1e-14, shrink=0.5, max_iter=4000):
    """Projected pattern search for max of f_C on D (projection = radial retraction).

    Vectorised over the 8 probe directions; converges linearly in the shrinking step,
    which is what a Lipschitz/cone-shaped peak needs.
    """
    C = np.asarray(C, float)
    x = np.array(x0, float)
    if np.hypot(*x) > 1.0:
        x = x / np.hypot(*x)
    fx = f_min(x, C)
    D = _dirs()
    step, it = step0, 0
    while step > tol and it < max_iter:
        it += 1
        Y = x + step * D
        nrm = np.hypot(Y[:, 0], Y[:, 1])
        over = nrm > 1.0
        Y[over] = Y[over] / nrm[over, None]
        vals = fmin_grid(Y, C)
        k = int(np.argmax(vals))
        if vals[k] > fx:
            x, fx = Y[k], float(vals[k])
        else:
            step *= shrink
    return x, fx


def R_ref(C, n_grid=1001, topk=24, step0=0.05):
    """Reference max by dense grid + projected pattern search from the top-k cells.

    Returns dict with value, argmax, n_nearest, grid value, per-cell classification.
    """
    C = np.asarray(C, dtype=float)
    P = _grid_points(n_grid)
    F = fmin_grid(P, C)
    order = np.argsort(F)[::-1][:topk]
    best, bx = float(F[order[0]]), P[order[0]]
    for idx in order:
        x, v = pattern_search(P[idx], C, step0=step0)
        if v > best:
            best, bx = v, x
    ns = nearest_set(bx, C)
    return dict(value=best, argmax=bx, n_nearest=len(ns), nearest=ns,
                grid_value=float(F[order[0]]), grid_arg=P[order[0]])


def classify_argmax(C, x, tol=1e-9):
    """Classify a (candidate) maximizer into the degeneracy taxonomy."""
    C = np.asarray(C, dtype=float)
    x = np.asarray(x, float)
    ns = nearest_set(x, C, tol=1e-9)
    r = np.hypot(*x)
    tags = []
    if r < 1.0 - 1e-9:
        tags.append("intD")
    else:
        tags.append("bdD")
    if len(ns) == 1:
        tags.append("|argmin|=1")
        i = ns[0]
        a = antipode(C[i])
        if a is not None and np.hypot(*(x - a)) < 1e-7:
            tags.append("antipode(b)")
        if np.hypot(*(C[i])) < 1e-14:
            tags.append("origin-plateau")
    else:
        tags.append(f"|argmin|={len(ns)}")
    # is x a pair-bisector point?
    for i, j in itertools.combinations(range(len(C)), 2):
        if abs(np.hypot(*(x - C[i])) - np.hypot(*(x - C[j]))) < 1e-9:
            if np.hypot(*(C[i] - C[j])) > 1e-12:
                tags.append("on-bisector")
                break
    return tags, ns
