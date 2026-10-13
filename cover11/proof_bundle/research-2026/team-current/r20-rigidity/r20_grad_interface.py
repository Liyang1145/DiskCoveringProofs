"""r20-rigidity step 8: INTERFACE CHECK on the 18 active gradients.

An incoming interface (r20-chain) assumes the 18 active gradient rows are linearly
DEPENDENT in the 21-dim rotation slice (rank 17, exact positive relation
sum w_i g_i = 0, kernel dim 4).  My finite-difference J says rank 18 with
sigma_18 = 2.411e-9.  This script recomputes the same 18 gradients ANALYTICALLY
(closed-form chain rule, mpmath 60 dps, exact rational centres) and checks:
   V1 analytic J vs finite-difference J (max abs difference)
   V2 exact-rational determinant of a pivoted 18x18 minor of the ANALYTIC matrix
   V3 sigma_min of the analytic matrix (60-dps mpmath SVD)
"""
import json, math, itertools
from pathlib import Path
import numpy as np
import mpmath as mp

P = Path(__file__).parent
ROOT = P.parents[2]
mp.mp.dps = 60
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
C64 = np.array([[int(v) / 1e17 for v in a] for a in raw['centers_scaled_1e17']])
cal = json.loads((P / 'r20_calibration.json').read_text(encoding='utf-8'))
tight = cal['B']['tight_points']
n = 11
CM = [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** 17 for v in a]) for a in raw['centers_scaled_1e17']]


def dot(a, b):
    return sum(a[t] * b[t] for t in range(2))


def solve2(M, r):
    det = M[0, 0] * M[1, 1] - M[0, 1] * M[1, 0]
    return mp.matrix([(r[0, 0] * M[1, 1] - M[0, 1] * r[1, 0]) / det,
                      (M[0, 0] * r[1, 0] - r[0, 0] * M[1, 0]) / det])


def grad_V3(C, tri):
    """analytic gradient of the circumradius of triple tri (equidistance distance)"""
    a, b, c = tri
    d1 = C[b] - C[a]
    d2 = C[c] - C[a]
    D1 = (dot(C[b], C[b]) - dot(C[a], C[a])) / 2
    D2 = (dot(C[c], C[c]) - dot(C[a], C[a])) / 2
    M = mp.matrix([[d1[0], d1[1]], [d2[0], d2[1]]])
    u = solve2(M, mp.matrix([D1, D2]))
    r = u - C[a]
    f = mp.sqrt(dot(r, r))
    rh = r / f
    G = np.zeros(22)
    for alpha, kind in ((a, 'a'), (b, 'b'), (c, 'c')):
        for t in range(2):
            e = mp.matrix([1 if t == 0 else 0, 1 if t == 1 else 0])
            dM = mp.matrix(2, 2)
            drhs = mp.matrix([mp.mpf(0), mp.mpf(0)])
            dca = mp.matrix([mp.mpf(0), mp.mpf(0)])
            if kind == 'a':
                dca = e
                dM[0, 0] = -e[0, 0]; dM[0, 1] = -e[1, 0]
                dM[1, 0] = -e[0, 0]; dM[1, 1] = -e[1, 0]
                drhs[0, 0] = -dot(C[a], e); drhs[1, 0] = -dot(C[a], e)
            elif kind == 'b':
                dM[0, 0] = e[0, 0]; dM[0, 1] = e[1, 0]
                drhs[0, 0] = dot(C[b], e)
            else:
                dM[1, 0] = e[0, 0]; dM[1, 1] = e[1, 0]
                drhs[1, 0] = dot(C[c], e)
            du = solve2(M, drhs - dM * u)
            G[2 * alpha + t] = rh[0, 0] * (du[0, 0] - dca[0, 0]) + rh[1, 0] * (du[1, 0] - dca[1, 0])
    return G


def grad_V2b(C, sites, sgn):
    """analytic gradient of |p - c_i|, p = the boundary bisector point of (i,j)"""
    i, j = sites
    G = np.zeros(22)
    d = C[i] - C[j]
    D = dot(d, d)
    Del = (dot(C[i], C[i]) - dot(C[j], C[j])) / 2
    A0 = (Del / D) * d
    dn = mp.matrix([-d[1], d[0]]) / mp.sqrt(D)
    s = mp.sqrt(1 - dot(A0, A0))
    p = A0 + sgn * s * dn
    r = p - C[i]
    f = mp.sqrt(dot(r, r))
    rh = r / f
    for alpha in (i, j):
        for t in range(2):
            e = mp.matrix([1 if t == 0 else 0, 1 if t == 1 else 0])
            dd = mp.matrix([mp.mpf(0), mp.mpf(0)])
            dDel = mp.mpf(0)
            dci = mp.matrix([mp.mpf(0), mp.mpf(0)])
            if alpha == i:
                dd = e; dDel = dot(C[i], e); dci = e
            else:
                dd = -e; dDel = -dot(C[j], e)
            dD = 2 * dot(d, dd)
            dA0 = (dDel / D) * d + (Del / D) * dd - (Del * dD / D ** 2) * d
            ddn = mp.matrix([-dd[1], dd[0]]) / mp.sqrt(D) - mp.matrix([-d[1], d[0]]) * dot(d, dd) / D ** mp.mpf('1.5')
            ds = -dot(A0, dA0) / s
            dp = dA0 + sgn * (ds * dn + s * ddn)
            G[2 * alpha + t] = rh[0, 0] * (dp[0, 0] - dci[0, 0]) + rh[1, 0] * (dp[1, 0] - dci[1, 0])
    return G


JA = np.zeros((18, 22))
for r, p in enumerate(tight):
    if p['kind'] == 'V3':
        JA[r] = [float(x) for x in grad_V3(CM, tuple(p['sites']))]
    else:
        i, j = p['sites']
        dv = C64[i] - C64[j]
        dd = float(dv @ dv)
        A0 = (0.5 * (C64[i] @ C64[i] - C64[j] @ C64[j]) / dd) * dv
        nv = np.array([-dv[1], dv[0]]) / math.sqrt(dd)
        sgn = 1 if ((np.array(p['point']) - A0) @ nv) > 0 else -1
        JA[r] = [float(x) for x in grad_V2b(CM, (i, j), sgn)]

J = np.load(P / 'r20_J60.npy')
print('V1  analytic vs finite-difference J : max |diff| = %.3e   (||J||_max = %.3f)'
      % (np.abs(JA - J).max(), np.abs(J).max()))
U, S, Vt = np.linalg.svd(JA)
print('V3  analytic J singular values: last 3 =', S[-3:], ' rank at 1e-12 rel:',
      int((S > 1e-12 * S[0]).sum()))
# exact rational determinant of a column-pivoted 18x18 minor
from fractions import Fraction
from scipy.linalg import qr as spqr
Q, R, perm = spqr(JA, pivoting=True, mode='economic')
cols = [int(t) for t in perm[:18]]
M = [[Fraction(float(JA[i, c])) for c in cols] for i in range(18)]
A = [row[:] for row in M]
det = Fraction(1)
for k in range(18):
    p_ = None
    for i2 in range(k, 18):
        if A[i2][k] != 0:
            p_ = i2; break
    if p_ is None:
        det = Fraction(0); break
    if p_ != k:
        A[k], A[p_] = A[p_], A[k]; det = -det
    det *= A[k][k]
    for i2 in range(k + 1, 18):
        if A[i2][k] == 0:
            continue
        f_ = A[i2][k] / A[k][k]
        for j2 in range(k, 18):
            A[i2][j2] -= f_ * A[k][j2]
print('V2  exact rational det of pivoted 18x18 minor: %s   (log10|det| = %s)'
      % ('NONZERO' if det != 0 else 'ZERO',
         ('%.2f' % math.log10(abs(float(det)))) if det != 0 else '-'))
print('    cond of that minor = %.2e' % np.linalg.cond(JA[:, cols]))
np.save(P / 'r20_JA_analytic.npy', JA)
