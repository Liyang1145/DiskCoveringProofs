"""Full critical set of the saved candidate with the CORRECT list of binding points.

Critical points of the covering-radius function for 11 disks covering the unit disk D
with equal radius R:
  (i) Voronoi vertices of the 11 sites inside D  (3 sites, generic)
  (ii) boundary points of D equidistant from the two adjacent ring sites
       (the "spokes", one per consecutive ring pair).
R_cov = max over this finite set of the nearest-site distance.  The saved object is
supposed to satisfy R_cov = R (certified upper bound).  Calibration only.
"""
import json, io, math, itertools
import numpy as np
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
C = [(int(a) / 1e17, int(b) / 1e17) for a, b in D['centers_scaled_1e17']]
R = float(D['certified_interval']['lo'])
n = 11
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]
H0, H2 = 0, 2


def nearest(p):
    return min(range(n), key=lambda i: (p[0] - C[i][0]) ** 2 + (p[1] - C[i][1]) ** 2)


def dist(p, i):
    return math.hypot(p[0] - C[i][0], p[1] - C[i][1])


def main():
    print('R (certified lo) = %.20f' % R)
    # --- Voronoi vertices inside D ---
    verts = []
    seen = set()
    for tri in itertools.combinations(range(n), 3):
        A, B, Cc = C[tri[0]], C[tri[1]], C[tri[2]]
        d1 = B[0] - A[0]; d2 = B[1] - A[1]; e1 = Cc[0] - A[0]; e2 = Cc[1] - A[1]
        den = d1 * e2 - d2 * e1
        if abs(den) < 1e-18:
            continue
        bx = ((B[0] ** 2 + B[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
        by = ((Cc[0] ** 2 + Cc[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
        ux = (bx * e2 - by * d2) / den
        uy = (d1 * by - e1 * bx) / den
        if ux * ux + uy * uy > 1:
            continue
        key = (round(ux, 13), round(uy, 13))
        if key in seen:
            continue
        seen.add(key)
        ds = sorted(((dist((ux, uy), t), t) for t in range(n)))
        verts.append((ds[0][0], ux, uy, tri, ds[:3]))

    # --- spokes: intersection of bd D with the perpendicular bisector of consecutive rings ---
    ang = sorted([(math.atan2(C[i][1], C[i][0]) % (2 * math.pi), i) for i in RINGS])
    order = [i for a, i in ang]
    spokes = []
    for k in range(9):
        i = order[k]; j = order[(k + 1) % 9]
        a = ang[k][0]; b = ang[(k + 1) % 9][0]
        if b < a:
            b += 2 * math.pi
        # point on bd D equidistant from both (solves |p-ci| = |p-cj| on the circle)
        ci, cj = np.array(C[i]), np.array(C[j])
        d = cj - ci
        # line: p.d = (|cj|^2-|ci|^2)/2
        t = ((cj @ cj) - (ci @ ci)) / 2
        nrm = d @ d
        f = d * (t / nrm)
        rem = 1 - f @ f
        if rem < 0:
            print('spoke(%d,%d) no intersection' % (i, j)); continue
        s = math.sqrt(rem) / math.sqrt(nrm)
        cands = [f - s * np.array([-d[1], d[0]]), f + s * np.array([-d[1], d[0]])]
        pick = None
        for p in cands:
            th = math.atan2(p[1], p[0]) % (2 * math.pi)
            if th < a:
                th += 2 * math.pi
            if a - 1e-9 <= th <= b + 1e-9:
                pick = p
        if pick is None:
            print('spoke(%d,%d) branch not found' % (i, j)); continue
        ds = sorted(((dist(pick, t2), t2) for t2 in range(n)))
        spokes.append((ds[0][0], pick[0], pick[1], (i, j), ds[:3]))

    allpts = [(v[0], 'vert', v) for v in verts] + [(s[0], 'spoke', s) for s in spokes]
    allpts.sort(reverse=True)
    print('\ncritical set sorted by nearest-site distance (top 24):')
    for val, kind, rec in allpts[:24]:
        print('  %.20f  %-5s' % (val, kind), end='')
        if kind == 'vert':
            print(' v=(%+.15f,%+.15f) gen=%s nearest=%s' % (rec[1], rec[2], rec[3],
                  [(t, '%.12f' % x) for x, t in rec[4]]))
        else:
            print(' p=(%+.15f,%+.15f) pair=%s nearest=%s' % (rec[1], rec[2], rec[3],
                  [(t, '%.12f' % x) for x, t in rec[4]]))
    print('\nmax over critical set = %.20f' % allpts[0][0])
    print('number of critical points within 1e-14 of the max:',
          sum(1 for v, k, r in allpts if allpts[0][0] - v < 1e-14))
    print('number within 1e-3 above the max-1e-3 (i.e. nearly tight):',
          sum(1 for v, k, r in allpts if v > allpts[0][0] - 1e-3))
    # list all near-tight with their kind
    print('\nall critical points with R_cov - val < 2e-3:')
    for val, kind, rec in allpts:
        if allpts[0][0] - val < 2e-3:
            if kind == 'vert':
                print('  %.20f vert  gen=%s   d=%s' % (val, rec[3], ['%.6f' % x for x, t in rec[4]]))
            else:
                print('  %.20f spoke pair=%s   d=%s' % (val, rec[3], ['%.6f' % x for x, t in rec[4]]))


if __name__ == '__main__':
    main()
