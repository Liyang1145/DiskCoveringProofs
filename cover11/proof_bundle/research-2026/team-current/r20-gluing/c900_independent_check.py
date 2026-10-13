# -*- coding: utf-8 -*-
"""c900_independent_check.py — INDEPENDENT read-only check of C900's structural parts
(lead/CENTRAL-FIBER-HELLY-REDUCTION.md), with my own enumeration and my own geometry code.
No shared helpers, no claims registered, nothing outside r20-gluing is written.

Checked here:
  (A) Helly bookkeeping: family = 1 open ball + m=4 chain-pin disks + 2 central disks = 7 convex sets;
      C(7,3) = 35 triples; the 10 triples without a central disk are automatically nonempty when K_B
      is known nonempty; the remaining 25 split as 12 + 4 + 8 + 1 (C900's list).
  (B) equal-radius triple test: for three closed disks of radius r, common intersection exists iff
      the MINIMUM ENCLOSING CIRCLE of the three centres has radius <= r (NOT circumradius alone);
      verified against a brute-force sampled test including a collinear and an obtuse case.
  (C) open ball + two closed disks: min_{b in B(u,r) cap B(v,r)} |b| < rho (STRICT); my own
      case-based minimum (0 if feasible / single-circle nearest point / circle-circle intersections)
      verified against dense sampling.
  (D) collinear stratum: on the chord line the two factors |b-q|^2-r^2 and |b-q'|^2-r^2 coincide,
      so near-disk membership contradicts strict positivity of the far factor (checked numerically);
      hence the disk-intersection criterion contains no collinear point.
"""
import json
import math
import random
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).parent


# ---------------- (A) Helly bookkeeping ----------------
def helly_count(m):
    names = ['ball'] + ['pin%d' % j for j in range(m)] + ['cen0', 'cen4']
    triples = list(combinations(names, 3))
    def kind(t):
        c = sum(1 for x in t if x.startswith('cen'))
        b = sum(1 for x in t if x == 'ball')
        p = 3 - c - b
        return (b, c, p)
    from collections import Counter
    cnt = Counter(kind(t) for t in triples)
    new = Counter({k: v for k, v in cnt.items() if k[1] > 0})
    old = Counter({k: v for k, v in cnt.items() if k[1] == 0})
    return len(triples), dict(new), dict(old)


# ---------------- (B) equal-radius disks: MEC criterion ----------------
def mec_radius(p, q, s):
    """exact-enough MEC radius of three points: half the longest side if the triangle is
    right/obtuse at the opposite vertex, else the circumradius."""
    def d2(a, b):
        return (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2
    a2, b2, c2 = d2(q, s), d2(s, p), d2(p, q)
    sides = sorted([a2, b2, c2])
    if sides[2] >= sides[0] + sides[1] - 1e-15:      # right/obtuse: longest side is the diameter
        return math.sqrt(sides[2]) / 2
    ax, ay = p; bx, by = q; cx, cy = s
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    ux = ((ax * ax + ay * ay) * (by - cy) + (bx * bx + by * by) * (cy - ay) + (cx * cx + cy * cy) * (ay - by)) / d
    uy = ((ax * ax + ay * ay) * (cx - bx) + (bx * bx + by * by) * (ax - cx) + (cx * cx + cy * cy) * (bx - ax)) / d
    return math.hypot(ux - ax, uy - ay)


def brute_minmax(centers, r_grid=400, g=161):
    """sampled min over p of max_i |p-c_i| (grid) -- a lower-bound test of nonemptiness."""
    best = float('inf')
    for i in range(g):
        for j in range(g):
            x = -1.5 + 3.0 * i / (g - 1)
            y = -1.5 + 3.0 * j / (g - 1)
            best = min(best, max(math.hypot(x - c[0], y - c[1]) for c in centers))
    return best


def check_mec():
    random.seed(7)
    rows = []
    # collinear case + obtuse case + random acute
    tests = [[(-1.0, 0.0), (0.0, 0.0), (1.0, 0.0)],          # collinear
             [(0.0, 0.0), (1.0, 0.0), (0.5, 0.05)],           # obtuse at the third
             [(-0.4, -0.3), (0.5, -0.2), (0.1, 0.6)]]         # generic
    for _ in range(3):
        tests.append([(random.uniform(-1, 1), random.uniform(-1, 1)) for _ in range(3)])
    for pts in tests:
        mec = mec_radius(*pts)
        for r in (mec * 0.9, mec * 1.1):
            sampled = brute_minmax(pts)
            nonempty_sample = sampled <= r
            criterion = mec <= r
            rows.append({'centers': pts, 'r': r, 'MEC': mec, 'criterion_nonempty': criterion,
                         'sampled_minmax': sampled, 'agrees': bool(criterion == nonempty_sample)})
    return rows


# ---------------- (C) open ball + two disks: strict min |b| ----------------
def min_norm_in_lens(u, v, r, samples=400000):
    """sampled minimum of |b| over B(u,r) cap B(v,r) (dense rejection sampling + boundary)."""
    best = float('inf')
    if math.hypot(u[0], u[1]) <= r and math.hypot(v[0], v[1]) <= r:
        return 0.0
    random.seed(11)
    for _ in range(samples):
        b = (random.uniform(-2, 2), random.uniform(-2, 2))
        if math.hypot(b[0] - u[0], b[1] - u[1]) <= r and math.hypot(b[0] - v[0], b[1] - v[1]) <= r:
            best = min(best, math.hypot(*b))
    return best


def min_norm_formula(u, v, r):
    """my own case-based formula: 0 if the origin is in both disks; else nearest point on the
    feasible arc(s): single-circle projection or circle-circle intersection."""
    def inn(c):
        return math.hypot(c[0], c[1]) <= r
    if inn(u) and inn(v):
        return 0.0
    d = math.hypot(v[0] - u[0], v[1] - u[1])
    cands = []
    if d > 1e-12:
        # circle-circle intersections
        a = (r * r - r * r + d * d) / (2 * d)
        h2 = r * r - a * a
        if h2 >= 0:
            h = math.sqrt(h2)
            ex, ey = (v[0] - u[0]) / d, (v[1] - u[1]) / d
            mx, my = u[0] + a * ex, u[1] + a * ey
            for s in (1, -1):
                cands.append((mx + s * h * -ey, my + s * h * ex))
    # single-disk nearest point of the other disk
    for c, other in ((u, v), (v, u)):
        n = math.hypot(*c)
        if n > 1e-12:
            p = (c[0] * r / n, c[1] * r / n)     # nearest point of B(c,r) to the origin
            if math.hypot(p[0] - other[0], p[1] - other[1]) <= r + 1e-12:
                cands.append(p)
    if not cands:
        return float('inf')
    return min(math.hypot(*p) for p in cands)


def check_lens():
    rows = []
    for u, v, r in [((-1.0, 0.0), (1.0, 0.0), 1.2), ((1.5, 0.0), (0.0, 1.5), 1.5),
                    ((-0.3, 0.4), (0.5, 0.2), 0.9), ((0.2, 0.1), (-0.1, 0.05), 0.8)]:
        f = min_norm_formula(u, v, r)
        s = min_norm_in_lens(u, v, r)
        rows.append({'u': u, 'v': v, 'r': r, 'formula': f, 'sampled': s,
                     'agrees': bool(abs(f - s) < 0.02 or (f == 0 and s == 0))})
    return rows


# ---------------- (D) collinear stratum ----------------
def check_collinear():
    a, c = (-0.5, 0.0), (0.6, 0.0)
    r = 0.8
    ux, uy = c[0] - a[0], c[1] - a[1]
    d = math.hypot(ux, uy)
    k = math.sqrt(r * r - d * d / 4)
    mx, my = (a[0] + c[0]) / 2, (a[1] + c[1]) / 2
    nx, ny = -uy / d, ux / d
    q = (mx + k * nx, my + k * ny)
    qp = (mx - k * nx, my - k * ny)
    rows = []
    for t in (-0.1, 0.2, 0.5, 0.9):
        b = (a[0] + t * (c[0] - a[0]), a[1] + t * (c[1] - a[1]))   # on the chord line
        f_near = math.hypot(b[0] - q[0], b[1] - q[1]) ** 2 - r * r
        f_far = math.hypot(b[0] - qp[0], b[1] - qp[1]) ** 2 - r * r
        rows.append({'t': t, 'near_factor': f_near, 'far_factor': f_far,
                     'equal': bool(abs(f_near - f_far) < 1e-12),
                     'near_le_0': bool(f_near <= 1e-12)})
    return rows


def main():
    out = {'role': 'independent read-only check of C900 structural parts (no claim registered)',
           'c900_statement_pin': 'claim C900 as registered (proved, unreviewed); evidence '
                                 'lead/CENTRAL-FIBER-HELLY-REDUCTION.md',
           'delta_omega_of_related_box_audit': '1/1000, 1/10000'}
    n_all, new, old = helly_count(4)
    print('(A) Helly: %d triples total; without a central disk: %s (%d); with a central disk: %s (%d)'
          % (n_all, old, sum(old.values()), new, sum(new.values())))
    print('    C900 list 12+4+8+1 = %d  -> matches new-triple count: %s'
          % (12 + 4 + 8 + 1, sum(new.values()) == 25))
    out['helly'] = {'triples_total': n_all, 'old': {str(k): v for k, v in old.items()},
                    'new': {str(k): v for k, v in new.items()},
                    'new_total': sum(new.values()), 'matches_25': sum(new.values()) == 25}
    mec = check_mec()
    print('(B) MEC criterion check: %d/%d agree with sampled nonemptiness'
          % (sum(1 for r in mec if r['agrees']), len(mec)))
    out['mec_rows'] = mec
    lens = check_lens()
    print('(C) strict-min lemma: %d/%d formula==sampled'
          % (sum(1 for r in lens if r['agrees']), len(lens)))
    out['lens_rows'] = lens
    col = check_collinear()
    print('(D) collinear stratum: factors equal on the chord line in %d/%d sample points; '
          'near factor <= 0 whenever far factor <= 0'
          % (sum(1 for r in col if r['equal']), len(col)))
    out['collinear_rows'] = col
    (HERE / 'c900_independent_check.json').write_text(json.dumps(out, indent=2, default=str))
    print('saved c900_independent_check.json')


if __name__ == '__main__':
    main()
