"""Active-set reconstruction for the saved n11 upper candidate (calibration ONLY).

Object: n11/upper/certified_object.json (22 integers / 10^17). Caliber: unit closed disk D,
equal disks radius R, centers in units of D's radius. All numbers here are double
precision unless explicitly labelled exact; nothing in this file is a certificate.

Goal of this file: determine WHICH constraints are active at the saved candidate, i.e.
(a) which boundary spokes are tight (ring-disk boundary arcs exactly meet on bd D),
(b) which Voronoi vertices are tight (nearest-site distance == R inside D),
(c) the incidence structure of those tight points.
"""
import json, io, math, itertools, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
OBJ = ROOT / 'n11' / 'upper' / 'certified_object.json'

def load():
    d = json.load(io.open(OBJ, encoding='utf-8-sig'))
    S = 10 ** 17
    C = [(int(a) / S, int(b) / S) for a, b in d['centers_scaled_1e17']]
    return d, C

def main():
    d, C = load()
    n = len(C)
    lo = float(d['certified_interval']['lo'])
    print('authoritative interval lo = %.54f' % lo)
    R = lo
    R2 = R * R
    rings = [i for i in range(n) if math.hypot(*C[i]) > 1 - R]
    hubs = [i for i in range(n) if i not in rings]
    print('n=%d  ring sites=%s  hubs=%s' % (n, rings, hubs))

    def d2(p, i):
        return (p[0] - C[i][0]) ** 2 + (p[1] - C[i][1]) ** 2

    # ---------- (a) boundary spokes induced by the ring order ----------
    ang = sorted([(math.atan2(C[i][1], C[i][0]) % (2 * math.pi), i) for i in rings])
    order = [i for a, i in ang]
    print('\nring angular order:', order, '(deg:', [round(math.degrees(a), 4) for a, i in ang], ')')
    spoke = []
    for k in range(len(order)):
        i = order[k]; j = order[(k + 1) % len(order)]
        a = ang[k][0]; b = ang[(k + 1) % len(order)][0]
        if b < a:
            b += 2 * math.pi
        m = (a + b) / 2
        p = (math.cos(m), math.sin(m))
        si = math.hypot(*C[i]); sj = math.hypot(*C[j])
        di = math.hypot(p[0] - C[i][0], p[1] - C[i][1])
        dj = math.hypot(p[0] - C[j][0], p[1] - C[j][1])
        di2 = math.hypot(d2(p, i), 0) ** .5
        m_i = math.sqrt(d2(p, i)); m_j = math.sqrt(d2(p, j))
        nearest = min(range(n), key=lambda t: d2(p, t))
        spoke.append(dict(i=i, j=j, mid=m, p=p, mi=m_i, mj=m_j))
        print('spoke(%2d,%2d) mid=%+9.5f deg  |.-c_i|=%.17f  |.-c_j|=%.17f  nearest=%d (%.12f)  %s'
              % (i, j, math.degrees(m % (2 * math.pi)), m_i, m_j, nearest, math.sqrt(d2(p, nearest)),
                 'TIGHT' if abs(m_i - R) < 1e-14 and abs(m_j - R) < 1e-14 else 'not tight'))
    # independent check: the boundary condition w_i + w_j = gap
    print('\nboundary capacity check  w_i + w_j - gap  (0 <=> both spokes saturate):')
    worst = 0.0
    for k in range(len(order)):
        i = order[k]; j = order[(k + 1) % len(order)]
        a = ang[k][0]; b = ang[(k + 1) % len(order)][0]
        if b < a:
            b += 2 * math.pi
        si = math.hypot(*C[i]); sj = math.hypot(*C[j])
        wi = math.acos(max(-1, min(1, (1 + si * si - R2) / (2 * si))))
        wj = math.acos(max(-1, min(1, (1 + sj * sj - R2) / (2 * sj))))
        worst = max(worst, abs(wi + wj - (b - a)))
        print('  (%2d,%2d) gap=%.15f  w_i+w_j=%.15f  diff=%+.3e' % (i, j, b - a, wi + wj, wi + wj - (b - a)))
    print('  max |w_i+w_j-gap| over the 9 spokes = %.3e' % worst)

    # ---------- (b) Voronoi vertices inside D ----------
    print('\nVoronoi vertices inside D, sorted by nearest-site radius (descending):')
    rows = []
    for tri in itertools.combinations(range(n), 3):
        P, Q, W = C[tri[0]], C[tri[1]], C[tri[2]]
        D0 = 2 * (P[0] * (Q[1] - W[1]) + Q[0] * (W[1] - P[1]) + W[0] * (P[1] - Q[1]))
        if D0 == 0:
            continue
        ux = ((P[0] ** 2 + P[1] ** 2) * (Q[1] - W[1]) + (Q[0] ** 2 + Q[1] ** 2) * (W[1] - P[1])
              + (W[0] ** 2 + W[1] ** 2) * (P[1] - Q[1])) / D0
        uy = ((P[0] ** 2 + P[1] ** 2) * (W[0] - Q[0]) + (Q[0] ** 2 + Q[1] ** 2) * (P[0] - W[0])
              + (W[0] ** 2 + W[1] ** 2) * (Q[0] - P[0])) / D0
        if ux * ux + uy * uy > 1:
            continue
        ds = sorted([(d2((ux, uy), t), t) for t in range(n)])
        rows.append((ds[0][0], ux, uy, tri, ds[0][1]))
    rows.sort(reverse=True)
    seen = set()
    tight = []
    for r2, x, y, tri, act in rows:
        key = (round(x, 13), round(y, 13))
        if key in seen:
            continue
        seen.add(key)
        r = math.sqrt(r2)
        if r > R - 5e-3:
            ns = sorted([(math.sqrt(d2((x, y), t)), t) for t in range(n)])
            tight.append((r, (x, y), tri, ns[:4]))
    for r, p, tri, ns in tight:
        print('  R_v=%.17f  v=(%+.15f,%+.15f) gen=%s  nearest=%s' %
              (r, p[0], p[1], tri, [(t, '%.12f' % v) for v, t in ns]))
    print('\n  number of vertices with R_v within 5e-3 of R: %d' % len(tight))
    return dict(order=order, tight=tight, spoke=spoke)

if __name__ == '__main__':
    main()
