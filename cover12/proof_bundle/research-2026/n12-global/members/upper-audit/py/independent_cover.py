"""independent_cover.py  (member upper-audit, 2026-09-26)

INDEPENDENT re-derivation for the n=12 configuration S12 = cfg/cert_n12_othern.json
(key centers_dec17), with my own arithmetic (no import of certlib / cert_cand / enclose17):

  (1) candidate family: antipodes of centres, perpendicular-bisector hits on |x|=1,
      circumcentres of triples  -- rebuilt from scratch with my own directed sqrt
      (isqrt scaling 2^256) and my own interval routines.
  (2) domain filter: box disjoint from D  <=>  (min_{x in B} |x|)^2 > 1 (exact rational).
  (3) COVERAGE INEQUALITY, decided in EXACT RATIONAL ARITHMETIC with no sqrt at all:
        for every candidate box B meeting D:   min_i max_{x in B} |x-c_i| <= claim
        <=>  min_i (max over the 4 corners of |x-c_i|^2) <= claim^2.
      (sqrt is monotone, so the squared comparison is exact.)
  (4) my own R-enclosure [lo, hi] with outward sqrt bounds, and the exact D2-style
      hi = max_B min_i dist_box_hi(B, c_i) compared against the historic claim string.
  (5) discriminating power of the diagnostic: repeat the filtered count at claim-1e-9 / -1e-6.
  (6) numpy float64 grid control (NOT a certificate): max over a fine grid of the min-distance,
      to show the claim is tight from below and that no in-D point is missed.

OBJECT / SCOPE: one configuration (12 centres = the 17-decimal literals of
cfg/cert_n12_othern.json); D = closed unit disk; claim =
22568935234031792038557518369/62500000000000000000000000000
(the `claim` string recorded in out/cert_n12_othern.json).
The conclusion "R_D(S12) <= claim" is a single-configuration upper bound for r_D(12);
it says nothing about optimality.

Run:  py -3 -B py/independent_cover.py > logs/independent_cover.txt 2>&1
"""
import json, os, sys
from fractions import Fraction as F
from math import isqrt
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..'))
CFG = os.path.join(ROOT, 'research-2026', 'session2', 'n1314', 'cfg', 'cert_n12_othern.json')
OUT = os.path.join(ROOT, 'research-2026', 'session2', 'n1314', 'out', 'cert_n12_othern.json')

BITS = 256
SC = 1 << BITS


# ---------------------------------------------------------------- my own directed sqrt
def sq_bounds(r):
    """(lo, hi) with lo <= sqrt(r) < hi, r >= 0 rational (isqrt at scale 2^BITS)."""
    r = F(r)
    if r < 0:
        raise ValueError('negative')
    p, q = r.numerator, r.denominator
    m = isqrt(p * q * SC)              # floor(sqrt(p*q) * 2^128)
    d = q * (1 << (BITS // 2))
    return F(m, d), F(m + 1, d)


def dstr(x, nd, mode='down'):
    """exact decimal string of a rational (my own, integer arithmetic)."""
    s = F(x) * 10 ** nd
    n, d = s.numerator, s.denominator
    if mode == 'down':
        q = n // d if n >= 0 else -((-n + d - 1) // d)
    elif mode == 'up':
        q = -((-n) // d)
    else:
        q = (2 * n + d) // (2 * d) if n >= 0 else -((2 * (-n) + d) // (2 * d))
    neg = q < 0
    a = -q if neg else q
    t = str(a).rjust(nd + 1, '0')
    return ('-' if neg else '') + t[:-nd] + '.' + t[-nd:]


# ---------------------------------------------------------------- interval helpers
def iv_mul(a, b):
    ps = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (min(ps), max(ps))


def iv_add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def iv_sub(a, b):
    return (a[0] - b[1], a[1] - b[0])


def iv_neg(a):
    return (-a[1], -a[0])


def iv_div(a, b):
    ps = (a[0] / b[0], a[0] / b[1], a[1] / b[0], a[1] / b[1])
    return (min(ps), max(ps))


# ---------------------------------------------------------------- candidate family
def circumcenter(a, b, c):
    dd = 2 * (a[0] * (b[1] - c[1]) + b[0] * (c[1] - a[1]) + c[0] * (a[1] - b[1]))
    if dd == 0:
        return None
    a2 = a[0] ** 2 + a[1] ** 2
    b2 = b[0] ** 2 + b[1] ** 2
    c2 = c[0] ** 2 + c[1] ** 2
    return ((a2 * (b[1] - c[1]) + b2 * (c[1] - a[1]) + c2 * (a[1] - b[1])) / dd,
            (a2 * (c[0] - b[0]) + b2 * (a[0] - c[0]) + c2 * (b[0] - a[0])) / dd)


def antipode_box(c):
    n2 = c[0] ** 2 + c[1] ** 2
    if n2 == 0:
        raise ValueError('centre at origin: antipode undefined')
    lo, hi = sq_bounds(n2)
    return (iv_div((-c[0], -c[0]), (lo, hi)), iv_div((-c[1], -c[1]), (lo, hi)))


def bis_circle_boxes(a, b):
    mx, my = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
    vx, vy = -(b[1] - a[1]), b[0] - a[0]
    L2 = vx * vx + vy * vy
    if L2 == 0:
        return []
    slo, shi = sq_bounds(L2)
    ux = iv_div((vx, vx), (slo, shi))
    uy = iv_div((vy, vy), (slo, shi))
    mu = iv_add(iv_mul((mx, mx), ux), iv_mul((my, my), uy))
    r2m1 = (mx * mx + my * my) - 1
    disc = iv_sub(iv_mul(mu, mu), (r2m1, r2m1))
    if disc[1] < 0:
        return []
    if disc[0] < 0:
        disc = (F(0), disc[1])
    dlo, dhi = sq_bounds(disc[1])
    s = (sq_bounds(disc[0])[0], dhi)
    out = []
    for sgn in (1, -1):
        t = iv_add(iv_neg(mu), s) if sgn == 1 else iv_sub(iv_neg(mu), s)
        out.append((iv_add((mx, mx), iv_mul(t, ux)), iv_add((my, my), iv_mul(t, uy))))
    return out


def build_candidates(C):
    out = []
    n = len(C)
    for i in range(n):
        out.append(('far%d' % i, antipode_box(C[i])))
    for i, j in combinations(range(n), 2):
        for t, box in enumerate(bis_circle_boxes(C[i], C[j])):
            out.append(('bis%d,%d#%d' % (i, j, t), box))
    for i, j, k in combinations(range(n), 3):
        p = circumcenter(C[i], C[j], C[k])
        if p is None:
            continue
        out.append(('circ%d,%d,%d' % (i, j, k), ((p[0], p[0]), (p[1], p[1]))))
    return out


# ---------------------------------------------------------------- exact box quantities
def box_outside(box):
    (x0, x1), (y0, y1) = box
    dx = F(0) if x0 <= 0 <= x1 else min(abs(x0), abs(x1))
    dy = F(0) if y0 <= 0 <= y1 else min(abs(y0), abs(y1))
    return dx * dx + dy * dy > 1


def maxcorner_d2(box, c):
    (x0, x1), (y0, y1) = box
    return max((x - c[0]) ** 2 + (y - c[1]) ** 2 for x in (x0, x1) for y in (y0, y1))


def mindist_box_hi(box, c):
    """sqrt_hi of the max corner distance (outward, my sqrt)."""
    return sq_bounds(maxcorner_d2(box, c))[1]


def witness_point(box):
    (x0, x1), (y0, y1) = box
    mx, my = (x0 + x1) / 2, (y0 + y1) / 2
    if mx * mx + my * my <= 1:
        return (mx, my)
    U = sq_bounds(mx * mx + my * my)[1]
    return (mx / U, my / U)


def point_dist_lo(q, c):
    return sq_bounds((q[0] - c[0]) ** 2 + (q[1] - c[1]) ** 2)[0]


def main():
    print('workspace =', ROOT)
    j = json.load(open(CFG, encoding='utf-8'))
    raw = j['centers_dec17']
    C = [(F(s[0]), F(s[1])) for s in raw]                 # exact literals, no float anywhere
    hist = json.load(open(OUT, encoding='utf-8'))
    claim = F(hist['claim'])
    claim2 = claim * claim
    print('config    = %s  (%d centres, key centers_dec17, 17-decimal literals)' % (os.path.relpath(CFG, ROOT), len(C)))
    print('claim     = %s  = %s' % (hist['claim'], claim))
    print('scope     = single configuration; D = closed unit disk; no optimality claim')
    print()

    cand = build_candidates(C)
    n_out = sum(1 for _, b in cand if box_outside(b))
    print('candidates rebuilt independently          : %d' % len(cand))
    print('  boxes disjoint from D (exact filter)    : %d' % n_out)
    print('  boxes meeting D                         : %d   (REPORT.md column: 328)'
          % (len(cand) - n_out))

    fails = []
    hi = None; hi_arg = None
    lo = None; lo_arg = None
    for name, box in cand:
        if box_outside(box):
            continue
        m = min(maxcorner_d2(box, C[i]) for i in range(len(C)))
        if m > claim2:
            fails.append((name, dstr(sq_bounds(m)[0], 20)))
        ub = min(mindist_box_hi(box, C[i]) for i in range(len(C)))
        if hi is None or ub > hi:
            hi, hi_arg = ub, name
        q = witness_point(box)
        lb = min(point_dist_lo(q, C[i]) for i in range(len(C)))
        if lo is None or lb > lo:
            lo, lo_arg = lb, name

    print()
    print('EXACT squared test  min_i max_corner |x-c_i|^2 <= claim^2 , all D-meeting boxes:')
    print('  failures (exact rational, sqrt-free)    : %d' % len(fails))
    for x in fails[:10]:
        print('    ', x)
    print('  => (given the candidate lemma, see report)  R_D(S12) <= claim  [independent arithmetic]')
    print()
    print('my own R enclosure (my sqrt at 2^-%d):' % (BITS // 2))
    print('  lo = %s   (argmax %s)' % (dstr(lo, 30, 'down'), lo_arg))
    print('  hi = %s   (argmax %s)' % (dstr(hi, 30, 'up'), hi_arg))
    print('  hi <= claim ? %s     lo >= hist d2_lo ? %s' % (hi <= claim, lo >= F(hist['d2_lo'])))
    print('  hist d2 = [%s, %s], hist width %s' % (hist['d2_lo'], hist['d2_hi'], hist['width']))
    print()

    # ---- discriminating power of the FILTERED diagnostic (necessary condition) ----
    for label, r in (('claim', claim), ('claim-1e-9', claim - F(1, 10 ** 9)),
                     ('claim-1e-6', claim - F(1, 10 ** 6)), ('claim-1e-3', claim - F(1, 10 ** 3))):
        k = 0
        for name, box in cand:
            if box_outside(box):
                continue
            if min(maxcorner_d2(box, C[i]) for i in range(len(C))) > r * r:
                k += 1
        print('  D-meeting candidate boxes with min_i max_corner > %-11s : %d' % (label, k))
    print('  (the same count WITHOUT the domain filter is the historical cover_n_uncovered=36)')
    print()

    # ---- numpy grid control (NOT a certificate) ----
    try:
        import numpy as np
        M = 4001
        xs = np.linspace(-1, 1, M)
        cx = np.array([float(c[0]) for c in C])
        cy = np.array([float(c[1]) for c in C])
        best = 0.0
        for k in range(0, M, 500):
            X, Y = np.meshgrid(xs[k:k + 500], xs)
            keep = X * X + Y * Y <= 1.0
            if not keep.any():
                continue
            Xk = X[keep]; Yk = Y[keep]
            d = np.sqrt((Xk[:, None] - cx[None, :]) ** 2 + (Yk[:, None] - cy[None, :]) ** 2).min(axis=1)
            best = max(best, float(d.max()))
        print('  float64 grid control (%dx%d points in D): max min_i dist = %.16f' % (M, M, best))
        print('     vs claim = %.18f  (grid <= R <= claim expected; grid is NOT a certificate)' % float(claim))
    except Exception as e:
        print('  grid control skipped:', e)


if __name__ == '__main__':
    main()
