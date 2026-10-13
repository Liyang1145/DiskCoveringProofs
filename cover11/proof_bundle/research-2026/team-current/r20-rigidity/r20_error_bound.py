"""r20-rigidity (step 14): the objective-deficit -> distance error bound at X60.

Ingredients (all from the cached 120-dps Hessians and the exact object):
  * Danskin multiplier u > 0, sum u_i grad f_i = 0  (first-order stationarity, exact in the
    interior of the normal cone).
  * Hbar = sum_i u_i H_i  (the "Danskin-average" Hessian).  For every direction v:
        max_i [ grad f_i . v + 1/2 v^T H_i v ] >= 1/2 v^T Hbar v ,
    because the left side is a max and the right side is the u-average.  Hence
        gamma(X60+d) >= gamma(X60) + 1/2 d^T Hbar d - K |d|^3 ,
    with K a bound on the third-order remainder.  Along the rotation generator Hbar = 0
    (gamma is exactly rotation invariant), so the bound is read modulo the rotation orbit.
  * The min-max certificate over ALL first-order flat directions (step 13) gives the
    complementary bound  max_i v^T H_i v >= 0.2555 |v|^2  on ker(J18)/rotation.

Reported below: the spectrum of Hbar on the rotation-orthogonal complement, the resulting
quadratic constant, and an estimate of the third-order remainder scale (diagnostic).
"""
import json, itertools
from pathlib import Path
import numpy as np
import mpmath as mp

P = Path(__file__).parent
ROOT = P.parents[2]
N = 11
z = np.load(P / 'r20_hess_cache.npz')
Hf, Jf = z['H'], z['J']
d = json.loads((P / 'r20_second_order_certificate.json').read_text(encoding='utf-8'))
raw = json.loads((ROOT / 'research-2026/session2/n11alg/cert_sym60.json').read_text(encoding='utf-8-sig'))
X64 = np.array([[int(v) / 1e60 for v in a] for a in raw['centers_scaled_1e60']])

# Danskin multiplier from J (float64 SVD; the 120-dps value is in the certificate JSON)
U, S, Vt = np.linalg.svd(Jf)
u = U[:, -1]
u = np.abs(u) / np.abs(u).sum()
print('u (Danskin multiplier, float64): min %.6e max %.6e ; ||J^T u||_inf = %.3e'
      % (u.min(), u.max(), np.abs(Jf.T @ u).max()))

Hbar = np.einsum('i,iab->ab', u, Hf)
Hbar = (Hbar + Hbar.T) / 2
rot = np.array([c for i in range(N) for c in (-X64[i, 1], X64[i, 0])])
rot = rot / np.linalg.norm(rot)
Pr = np.eye(22) - np.outer(rot, rot)
M = Pr @ Hbar @ Pr
M = (M + M.T) / 2
ev = np.linalg.eigvalsh(M)
print('spectrum of Hbar restricted to rot^perp (22 eigenvalues, ascending):')
print('  ', np.array2string(ev, precision=6, suppress_small=False))
print('lambda_min = %.6e   (=> quadratic error-bound constant 1/2 lambda_min = %.3e)'
      % (ev[0], ev[0] / 2))
print('rotation direction: rot^T Hbar rot = %.3e (must be 0)' % float(rot @ Hbar @ rot))

# cross-check: is Hbar positive semidefinite on the flat space ker/rotation?
ker = Vt[17:].T
Qk, _ = np.linalg.qr(ker - np.outer(rot, rot @ ker))
Qk = Qk[:, :4]
Af = Qk.T @ Hbar @ Qk
print('Hbar on the flat space: eigenvalues', np.array2string(np.linalg.eigvalsh(Af), precision=6))
print('min over flat space of the SDP certificate (max_i v^T H_i v)  = 0.2555  vs  Hbar on the same space')

# third-order remainder scale (diagnostic, sampling of directions; NOT a proof bound)
mp.mp.dps = 60
X = [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** 60 for v in a]) for a in raw['centers_scaled_1e60']]
tight = [(k, tuple(s)) for k, s in d['tight']]


def circ(C, tri):
    a, b, c = tri
    A = mp.matrix([[C[b][0] - C[a][0], C[b][1] - C[a][1]],
                   [C[c][0] - C[a][0], C[c][1] - C[a][1]]])
    rhs = mp.matrix([(sum(C[b][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2,
                     (sum(C[c][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2])
    return mp.lu_solve(A, rhs)


def bis_bd(C, i, j, sgn):
    dv = C[i] - C[j]
    d2 = sum(dv[t] ** 2 for t in range(2))
    A0 = mp.matrix([(sum(C[i][t] ** 2 for t in range(2)) - sum(C[j][t] ** 2 for t in range(2))) / 2
                    / d2 * dv[t] for t in range(2)])
    nv = mp.matrix([-dv[1] / mp.sqrt(d2), dv[0] / mp.sqrt(d2)])
    s2 = 1 - sum(A0[t] ** 2 for t in range(2))
    return mp.matrix([A0[t] + sgn * mp.sqrt(s2) * nv[t] for t in range(2)])


def dd(p, q):
    return mp.sqrt(sum((p[t] - q[t]) ** 2 for t in range(2)))


def fsg(i, j):
    dv = X64[i] - X64[j]
    d2 = dv @ dv
    A0 = (0.5 * (X64[i] @ X64[i] - X64[j] @ X64[j]) / d2) * dv
    nv = np.array([-dv[1], dv[0]]) / np.sqrt(d2)
    for sg in (1, -1):
        p = A0 + sg * np.sqrt(1 - A0 @ A0) * nv
        dv2 = np.linalg.norm(X64 - p, axis=1)
        if set(np.argsort(dv2)[:2]) == {i, j}:
            return sg


funs = []
for k, s in tight:
    if k == 'V3':
        funs.append(lambda C, s=s: dd(circ(C, s), C[s[0]]))
    else:
        sg = fsg(*s)
        funs.append(lambda C, i=s[0], j=s[1], g=sg: dd(bis_bd(C, i, j, g), C[i]))

rng = np.random.default_rng(11)
worst = 0.0
for trial in range(200):
    v = rng.normal(size=22)
    v = v - (v @ rot) * rot
    nv_ = np.linalg.norm(v)
    if nv_ < 1e-12:
        continue
    v = v / nv_
    t = 1e-3
    Cv = [mp.matrix([X[i][0] + mp.mpf(float(t * v[2 * i])), X[i][1] + mp.mpf(float(t * v[2 * i + 1]))])
          for i in range(N)]
    for i in range(18):
        g1 = sum(mp.mpf(float(Jf[i, a])) * mp.mpf(float(v[a])) for a in range(22))
        g2 = sum(mp.mpf(float(v[a])) * mp.mpf(float(Hf[i][a, b])) * mp.mpf(float(v[b]))
                 for a in range(22) for b in range(22))
        actual = funs[i](Cv) - mp.mpf(d['gamma'])
        pred = mp.mpf(float(t)) * g1 + mp.mpf(float(t)) ** 2 / 2 * g2
        rem = abs(actual - pred) / mp.mpf(float(t)) ** 3
        worst = max(worst, float(rem))
print('third-order remainder scale estimate (200 directions, t=1e-3): max |rem|/t^3 ~ %.4f' % worst)
print('=> for |d| <= rho the quadratic term dominates if 0.5*lambda_min*rho > K_pervec*rho^3,')
print('   i.e. rho < sqrt(0.5*%.3e/%.3f) = %.3e (using the 1D-direction constant scale)'
      % (ev[0], worst, (0.5 * abs(ev[0]) / max(worst, 1e-9)) ** 0.5))

json.dump({'u_min': float(u.min()), 'u_max': float(u.max()),
           'Hbar_spectrum': ev.tolist(), 'lambda_min_Hbar_rotperp': float(ev[0]),
           'quadratic_constant_half': float(ev[0] / 2),
           'rot_Hbar_rot': float(rot @ Hbar @ rot),
           'Hbar_on_flat_eigs': np.linalg.eigvalsh(Af).tolist(),
           'third_order_scale_estimate': worst,
           'rho_estimate': float((0.5 * abs(ev[0]) / max(worst, 1e-9)) ** 0.5)},
          open(P / 'r20_error_bound.json', 'w'), indent=2)
print('written r20_error_bound.json')
