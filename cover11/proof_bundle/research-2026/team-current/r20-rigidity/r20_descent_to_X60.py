"""r20-rigidity step 10: THE TRUE DESCENT — along the direction to the registered
symmetric object X60 (this corrects my step-2/step-7 "flat well" reading).

W4 of the predecessor's STATUS says: along the direction to rotated X60 the covering
radius decreases with slope ~7.17e-9 per unit distance, total -1.93e-17 at X60.
My earlier v18 test only measured the direction that decreases ALL 18 tight values
simultaneously (the thin Gordan cone, tau <= 6.6e-10) - that is a bound on the
simultaneous decrease, NOT on gamma = max_i f_i.

This script:
  D1  align X60 to x* (rotation minimising the sup-distance), report the distance
  D2  evaluate gamma (60 dps, full 20-point critical set) along the segment
      x*(s) = (1-s) x* + s X60_aligned, s = 0, 0.1, ..., 1
  D3  first-order check: slope of the argmax function V2b(1,7) along the segment
"""
import json, math, itertools
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60
P = Path(__file__).parent
ROOT = P.parents[2]
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
LO = mp.mpf(raw['certified_interval']['lo'])
T_CERT = mp.mpf('0.379983853119838689722261606136093214308718957')
COBJ = [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** 17 for v in a]) for a in raw['centers_scaled_1e17']]
d60 = json.loads((ROOT / 'research-2026/session2/n11alg/cert_sym60.json').read_text(encoding='utf-8-sig'))
X60 = [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** 60 for v in a]) for a in d60['centers_scaled_1e60']]
cal = json.loads((P / 'r20_calibration.json').read_text(encoding='utf-8'))
tight = cal['B']['tight_points']
n = 11


def dist(p, q):
    return mp.sqrt(sum((p[t] - q[t]) ** 2 for t in range(2)))


def rot(X, th):
    c, s = mp.cos(th), mp.sin(th)
    return [mp.matrix([X[i][0] * c - X[i][1] * s, X[i][0] * s + X[i][1] * c]) for i in range(11)]


def supd(A, B):
    return max(min(dist(A[i], B[j]) for j in range(11)) for i in range(11))


# ---- D1 alignment ---------------------------------------------------------
best = (mp.mpf(1e9), mp.mpf(0))
for k in range(-4000, 4001):
    th = mp.mpf(k) * mp.pi / 4000
    v = supd(COBJ, rot(X60, th))
    if v < best[0]:
        best = (v, th)
th0 = best[1]
step = mp.pi / 4000
for _ in range(60):
    step /= 2
    for s in (-1, 0, 1):
        v = supd(COBJ, rot(X60, th0 + s * step))
        if v < best[0]:
            best = (v, th0 + s * step)
        th0 = best[1]
Xr = rot(X60, best[1])
print('D1  aligned: sup-distance = %.6e at theta = %s rad ; Euclidean ||x* - X60|| = %.6e'
      % (float(best[0]), mp.nstr(best[1], 12),
         float(mp.sqrt(sum(sum((COBJ[i][t] - Xr[i][t]) ** 2 for t in range(2)) for i in range(11))))))


# ---- gamma on the full 20-point critical set -----------------------------
def circ(C, tri):
    a, b, c = tri
    A = mp.matrix([[C[b][0] - C[a][0], C[b][1] - C[a][1]],
                   [C[c][0] - C[a][0], C[c][1] - C[a][1]]])
    rhs = mp.matrix([(sum(C[b][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2,
                     (sum(C[c][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2])
    return mp.lu_solve(A, rhs)


def gamma20(C):
    vals = []
    for (i, j, k) in itertools.combinations(range(11), 3):
        try:
            u = circ(C, (i, j, k))
        except ZeroDivisionError:
            continue
        if sum(u[t] ** 2 for t in range(2)) > 1:
            continue
        vals.append(min(dist(u, C[q]) for q in range(11)))
    for i2 in range(11):
        for j2 in range(i2 + 1, 11):
            dv = C[i2] - C[j2]
            dd = sum(dv[t] ** 2 for t in range(2))
            if dd == 0:
                continue
            A0 = mp.matrix([(sum(C[i2][t] ** 2 for t in range(2)) - sum(C[j2][t] ** 2 for t in range(2))) / 2
                            / dd * dv[t] for t in range(2)])
            nv = mp.matrix([-dv[1] / mp.sqrt(dd), dv[0] / mp.sqrt(dd)])
            s2 = 1 - sum(A0[t] ** 2 for t in range(2))
            if s2 <= 0:
                continue
            s = mp.sqrt(s2)
            for sg in (1, -1):
                p = mp.matrix([A0[t] + sg * s * nv[t] for t in range(2)])
                ds = sorted([(dist(p, C[q]), q) for q in range(11)])
                if {ds[0][1], ds[1][1]} == {i2, j2}:
                    vals.append(ds[0][0])
    return max(vals)


def lerp(s):
    return [mp.matrix([(1 - s) * COBJ[i][t] + s * XP[i][t] for t in range(2)]) for i in range(11)]


# correspondence x*_i  <->  Xr_{perm[i]}  (nearest-point matching at the aligned rotation)
XP = [None] * 11
for i in range(11):
    j = min(range(11), key=lambda q: dist(COBJ[i], Xr[q]))
    XP[i] = Xr[j]
print('D1b permutation x*_i <- Xr_j :', [min(range(11), key=lambda q: dist(COBJ[i], Xr[q])) for i in range(11)])
print('    sup |x*_i - XP_i| = %.4e ; Euclidean ||x* - XP|| = %.4e'
      % (float(max(dist(COBJ[i], XP[i]) for i in range(11))),
         float(mp.sqrt(sum(sum((COBJ[i][t] - XP[i][t]) ** 2 for t in range(2)) for i in range(11))))))


print('\nD2  gamma along x*(s) = (1-s)x* + s X60   [60 dps, 20-point critical set]')
print('     s        gamma - lo          gamma - gamma*')
for s in ('0', '0.001', '0.01', '0.05', '0.1', '0.25', '0.5', '0.75', '1'):
    ss = mp.mpf(s)
    g = gamma20(lerp(ss))
    print('   %-6s  %+.8e      %+.8e' % (s, g - LO, g - LO))

# ---- D3 argmax-function slope along the segment --------------------------
def f_V2b(C, sites, sgn):
    i, j = sites
    dv = C[i] - C[j]
    dd = sum(dv[t] ** 2 for t in range(2))
    A0 = mp.matrix([(sum(C[i][t] ** 2 for t in range(2)) - sum(C[j][t] ** 2 for t in range(2))) / 2
                    / dd * dv[t] for t in range(2)])
    nv = mp.matrix([-dv[1] / mp.sqrt(dd), dv[0] / mp.sqrt(dd)])
    s = mp.sqrt(1 - sum(A0[t] ** 2 for t in range(2)))
    p = mp.matrix([A0[t] + sgn * s * nv[t] for t in range(2)])
    return dist(p, C[i])


def f_list(C):
    out = []
    for p in tight:
        if p['kind'] == 'V3':
            u = circ(C, tuple(p['sites']))
            out.append((p['kind'], tuple(p['sites']), dist(u, C[p['sites'][0]])))
        else:
            i, j = p['sites']
            dv = C[i] - C[j]
            dd = sum(dv[t] ** 2 for t in range(2))
            A0 = mp.matrix([(sum(C[i][t] ** 2 for t in range(2)) - sum(C[j][t] ** 2 for t in range(2))) / 2
                            / dd * dv[t] for t in range(2)])
            nv = mp.matrix([-dv[1] / mp.sqrt(dd), dv[0] / mp.sqrt(dd)])
            sgn = 1 if sum((mp.matrix([mp.mpf(v) for v in p['point']])[t] - A0[t]) * nv[t]
                            for t in range(2)) > 0 else -1
            out.append((p['kind'], tuple(p['sites']), f_V2b(C, (i, j), sgn)))
    return out


h = mp.mpf('1e-12')
A1 = f_list(lerp(h)) if False else None
f0 = f_list(lerp(mp.mpf(0)))
f1 = f_list(lerp(h))
print('\nD3  per-function first-order slope along the segment (per unit s, s in [0,1]):')
rows = sorted(zip([(k, s) for (k, s, _) in f0], [float((b[2] - a[2]) / h) for a, b in zip(f0, f1)]),
              key=lambda t: t[1])
for (k, s), d in rows[:6]:
    print('    %-4s %-9s slope = %+.6e' % (k, str(s), d))
print('    ...')
for (k, s), d in rows[-3:]:
    print('    %-4s %-9s slope = %+.6e' % (k, str(s), d))
print('    argmax at s=0 : %s %s' % (f0[int(max(range(18), key=lambda i: f0[i][2]))][0],
                                     f0[int(max(range(18), key=lambda i: f0[i][2]))][1]))
print('    total drop of the max: gamma(X60) - gamma(x*) = %s' % mp.nstr(gamma20(Xr) - LO, 6))
