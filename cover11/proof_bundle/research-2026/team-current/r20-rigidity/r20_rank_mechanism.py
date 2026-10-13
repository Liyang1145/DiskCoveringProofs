"""r20-rigidity step 11: WHY the rank differs - X60 vs x*.

Mechanism hypothesis:
  * at the mirror-symmetric object X60 all 18 tight values are equal to 7.8e-61, so the
    argmax set is the FULL 18-tuple -> a first-order (Danskin) multiplier relation
    sum u_i grad f_i = 0 with u > 0 is exact there -> rank(J18) = 17.
  * at the stored rational candidate x* the values are tied only to 7.86e-17 and the
    argmax is unique (margin 9.3e-19) -> gamma is differentiable at x* with
    grad gamma = grad f_{argmax} != 0; there is no reason for a relation -> rank 18,
    sigma_18 = 2.4e-9 = (1.77e-9 symmetry breaking) x O(1) curvature.
This script builds J at the aligned+permuted X60 with the SAME 18 functions and compares.
"""
import json, math, itertools
from pathlib import Path
import numpy as np
import mpmath as mp

mp.mp.dps = 60
P = Path(__file__).parent
ROOT = P.parents[2]
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
COBJ = [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** 17 for v in a]) for a in raw['centers_scaled_1e17']]
d60 = json.loads((ROOT / 'research-2026/session2/n11alg/cert_sym60.json').read_text(encoding='utf-8-sig'))
X60 = [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** 60 for v in a]) for a in d60['centers_scaled_1e60']]
cal = json.loads((P / 'r20_calibration.json').read_text(encoding='utf-8'))
tight = cal['B']['tight_points']
n = 11


def dist(p, q):
    return mp.sqrt(sum((p[t] - q[t]) ** 2 for t in range(2)))


def circumcentre(C, tri):
    a, b, c = tri
    A = mp.matrix([[C[b][0] - C[a][0], C[b][1] - C[a][1]],
                   [C[c][0] - C[a][0], C[c][1] - C[a][1]]])
    rhs = mp.matrix([(sum(C[b][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2,
                     (sum(C[c][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2])
    return mp.lu_solve(A, rhs)


def boundary_point(C, i, j, sgn):
    dv = C[i] - C[j]
    dd = sum(dv[t] ** 2 for t in range(2))
    A0 = mp.matrix([(sum(C[i][t] ** 2 for t in range(2)) - sum(C[j][t] ** 2 for t in range(2))) / 2
                    / dd * dv[t] for t in range(2)])
    nv = mp.matrix([-dv[1] / mp.sqrt(dd), dv[0] / mp.sqrt(dd)])
    s = mp.sqrt(1 - sum(A0[t] ** 2 for t in range(2)))
    return mp.matrix([A0[t] + sgn * s * nv[t] for t in range(2)])


def f_of(kind, sites, sgn, C):
    if kind == 'V3':
        u = circumcentre(C, sites)
        return dist(u, C[sites[0]])
    return dist(boundary_point(C, sites[0], sites[1], sgn), C[sites[0]])


def build_J(Cbase_list):
    J = np.zeros((18, 22))
    h = mp.mpf('1e-20')
    for a, p in enumerate(tight):
        if p['kind'] == 'V3':
            kind, sites, sgn = 'V3', tuple(p['sites']), None
        else:
            i, j = p['sites']
            dv = COBJ[i] - COBJ[j]
            dd = float(sum(dv[t] ** 2 for t in range(2)))
            A0 = (0.5 * float(sum(COBJ[i][t] ** 2 - COBJ[j][t] ** 2 for t in range(2))) / dd) * np.array([float(dv[0]), float(dv[1])])
            nv = np.array([-float(dv[1]), float(dv[0])]) / math.sqrt(dd)
            pt = np.array(p['point'])
            sgn = 1 if (pt - A0) @ nv > 0 else -1
            kind, sites = 'V2b', (i, j)
        for k in range(n):
            for t in range(2):
                Cp = [mp.matrix(Cbase_list[i]) for i in range(n)]
                Cq = [mp.matrix(Cbase_list[i]) for i in range(n)]
                Cp[k][t] += h
                Cq[k][t] -= h
                J[a, 2 * k + t] = float((f_of(kind, sites, sgn, Cp) - f_of(kind, sites, sgn, Cq)) / (2 * h))
    return J


def analyse(tag, C):
    Jm = build_J(C)
    U, S, Vt = np.linalg.svd(Jm)
    ul = U[:, -1]
    print('%s' % tag)
    print('   last 3 singular values : %s' % np.array2string(S[-3:], precision=4))
    print('   left-null vector sign  : %s   (min %.4f)' % (''.join('+' if x > 0 else '-' for x in ul), ul.min()))
    lam = ul / ul.sum()
    res = np.linalg.norm(Jm.T @ lam)
    print('   min-norm positive relation residual ||J^T u|| = %.3e  (min u_i = %.4e)'
          % (res, lam.min()))
    vals = [float(f_of(('V3' if p['kind'] == 'V3' else 'V2b'),
                      tuple(p['sites']) if p['kind'] == 'V3' else tuple(p['sites']),
                      None if p['kind'] == 'V3' else
                      (1 if (np.array(p['point']) - np.array([0.0, 0.0])) @ np.array([0.0, 0.0]) > 0 else 1),
                      [mp.matrix(C[i]) for i in range(n)])) for p in tight]  # placeholder
    return Jm


# aligned + permuted X60 (same correspondence as the descent script)
def rot(X, th):
    c, s = mp.cos(th), mp.sin(th)
    return [mp.matrix([X[i][0] * c - X[i][1] * s, X[i][0] * s + X[i][1] * c]) for i in range(11)]


th_star = mp.mpf('-1.54745000444')
Xr = rot(X60, th_star)
XP = [Xr[min(range(11), key=lambda q: dist(COBJ[i], Xr[q]))] for i in range(11)]

analyse('J at the saved candidate x*  (labels/branches taken from x*)', COBJ)
analyse('J at X60 (aligned+permuted to x* labels)', XP)
