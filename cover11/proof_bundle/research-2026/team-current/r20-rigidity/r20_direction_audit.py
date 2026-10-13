"""r20-rigidity (step 10): audit of the direction/Jacobian interface.

Q5 of step 9 gave a constant slope d gamma/dt = -1.9326e-17 per unit t along the segment
x* -> aligned X60, i.e. -7.17e-9 per unit distance, while the 18-row Gordan dual bound of
step 9 (min over simplex of ||J^T lambda|| = 3.86e-9) allows at most -3.86e-9 per unit
distance.  Two computations cannot both be right.  This script decides which.

Direct (no FD Jacobian) high-precision audit:
  A1  directional derivative of each of the 18 tight functions along d, by central
      differences in t (h_t = 1e-15) -> vector gdir (18,)
  A2  the same from the FD Jacobian J (step 9) -> J d, compare
  A3  the actual 20-point critical max along the segment (t = 1e-6 .. 1e-2)
  A4  lambda in the simplex found by SLSQP: check sum, positivity, and the identity
      sum_i lambda_i (gdir_i) <= max_i gdir_i
"""
import json, itertools
from pathlib import Path
import numpy as np
import mpmath as mp

P = Path(__file__).parent
ROOT = P.parents[2]
DPS = 80
mp.mp.dps = DPS
N = 11

XS = [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** 17 for v in a])
      for a in json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))['centers_scaled_1e17']]
raw60 = json.loads((ROOT / 'research-2026/session2/n11alg/cert_sym60.json').read_text(encoding='utf-8-sig'))
X60 = [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** 60 for v in a]) for a in raw60['centers_scaled_1e60']]
LO = mp.mpf(json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
            ['certified_interval']['lo'])


def circ(C, tri):
    a, b, c = tri
    A = mp.matrix([[C[b][0] - C[a][0], C[b][1] - C[a][1]],
                   [C[c][0] - C[a][0], C[c][1] - C[a][1]]])
    rhs = mp.matrix([(sum(C[b][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2,
                     (sum(C[c][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2])
    return mp.lu_solve(A, rhs)


def bis_bd(C, i, j, sgn):
    dv = C[i] - C[j]
    dd_ = sum(dv[t] ** 2 for t in range(2))
    A0 = mp.matrix([(sum(C[i][t] ** 2 for t in range(2)) - sum(C[j][t] ** 2 for t in range(2))) / 2
                    / dd_ * dv[t] for t in range(2)])
    nv = mp.matrix([-dv[1] / mp.sqrt(dd_), dv[0] / mp.sqrt(dd_)])
    s2 = 1 - sum(A0[t] ** 2 for t in range(2))
    return None if s2 <= 0 else mp.matrix([A0[t] + sgn * mp.sqrt(s2) * nv[t] for t in range(2)])


def dd(p, q):
    return mp.sqrt(sum((p[t] - q[t]) ** 2 for t in range(2)))


def critical_set(C):
    crit = []
    for tri in itertools.combinations(range(N), 3):
        u = circ(C, tri)
        if u is None or sum(u[t] ** 2 for t in range(2)) > 1:
            continue
        ds = sorted((dd(u, C[q]), q) for q in range(N))
        if set(q for _, q in ds[:3]) == set(tri):
            crit.append((ds[0][0], 'V3', list(tri), None,
                         (lambda CC, s=tri: dd(circ(CC, s), CC[s[0]]))))
    for i, j in itertools.combinations(range(N), 2):
        for sgn in (1, -1):
            p = bis_bd(C, i, j, sgn)
            if p is None:
                continue
            ds = sorted((dd(p, C[q]), q) for q in range(N))
            if set(q for _, q in ds[:2]) == {i, j}:
                crit.append((ds[0][0], 'V2b', [i, j], sgn,
                             (lambda CC, a=i, b=j, g=sgn: dd(bis_bd(CC, a, b, g), CC[a]))))
    return crit


crits = critical_set(XS)
g0 = max(v for v, *_ in crits)
tight = [c for c in crits if c[0] > g0 - mp.mpf('1e-9')]
print('A0  #critical = %d  #tight = %d  gamma* = %s' % (len(crits), len(tight), mp.nstr(g0, 30)))
assert len(tight) == 18

# ---- aligned direction d  (same construction as step 9) --------------------
th_best, m_best = None, mp.inf
for k in range(0, 2000):
    th = 2 * mp.pi * k / 2000
    Rm = mp.matrix([[mp.cos(th), -mp.sin(th)], [mp.sin(th), mp.cos(th)]])
    worst = max(min(dd(Rm * X60[i], XS[j]) for j in range(N)) for i in range(N))
    if worst < m_best:
        m_best, th_best = worst, th
for scale in ('1e-3', '1e-5', '1e-7', '1e-9', '1e-11'):
    sc = mp.mpf(scale)
    for k in range(-50, 51):
        th = th_best + sc * mp.pi * k / 50
        Rm = mp.matrix([[mp.cos(th), -mp.sin(th)], [mp.sin(th), mp.cos(th)]])
        worst = max(min(dd(Rm * X60[i], XS[j]) for j in range(N)) for i in range(N))
        if worst < m_best:
            m_best, th_best = worst, th
Rm = mp.matrix([[mp.cos(th_best), -mp.sin(th_best)], [mp.sin(th_best), mp.cos(th_best)]])
X60r = [Rm * X60[i] for i in range(N)]
perm = [int(min(range(N), key=lambda j: dd(X60r[i], XS[j]))) for i in range(N)]
dvec = []
for i in range(N):
    src = X60r[perm.index(i)]
    dvec += [src[0] - XS[i][0], src[1] - XS[i][1]]
nd = mp.sqrt(sum(x ** 2 for x in dvec))
print('A1  |d| = %s ; axis = %s deg ; max deviation = %s'
      % (mp.nstr(nd, 8), mp.nstr(th_best * 180 / mp.pi, 10), mp.nstr(m_best, 8)))
dn = [x / nd for x in dvec]                       # unit vector


def shifted(base, t, vec):
    return [mp.matrix([base[i][0] + t * vec[2 * i], base[i][1] + t * vec[2 * i + 1]]) for i in range(N)]


h_t = mp.mpf('1e-15')
gdir = []
for v, kind, sites, sgn, f in tight:
    fp = f(shifted(XS, +h_t, dn))
    fm = f(shifted(XS, -h_t, dn))
    gdir.append((fp - fm) / (2 * h_t))
print('\nA1  directional derivatives of the 18 tight functions along the unit direction d-hat:')
for (v, kind, sites, sgn, f), gg in zip(tight, gdir):
    print('    %-4s %-12s  (f - gamma*) = %-12s   f\'(d) = %s'
          % (kind, str(sites), mp.nstr(v - g0, 5), mp.nstr(gg, 12)))
print('    max f\'(d) = %s   min f\'(d) = %s' % (mp.nstr(max(gdir), 12), mp.nstr(min(gdir), 12)))

# ---- J from step 9 (recompute the same way, then compare J d --------------
def grad16(rec_f, C, h=mp.mpf('1e-25')):
    g = []
    for i in range(N):
        for t in range(2):
            Cp = [mp.matrix(C[k]) for k in range(N)]
            Cm = [mp.matrix(C[k]) for k in range(N)]
            Cp[i][t] += h
            Cm[i][t] -= h
            g.append((rec_f(Cp) - rec_f(Cm)) / (2 * h))
    return g


J = [grad16(f, XS) for (v, kind, sites, sgn, f) in tight]
Jd = [sum(J[i][k] * dn[k] for k in range(22)) for i in range(18)]
print('\nA2  (J d)_i from the step-9 finite-difference Jacobian (h=1e-25):')
for (v, kind, sites, sgn, f), gg, jj in zip(tight, gdir, Jd):
    print('    %-4s %-12s  direct = %-14s  Jd = %-14s  diff = %s'
          % (kind, str(sites), mp.nstr(gg, 10), mp.nstr(jj, 10), mp.nstr(jj - gg, 4)))
print('    max (J d) = %s' % mp.nstr(max(Jd), 12))

# ---- A3: the actual critical max along the segment ------------------------
print('\nA3  20-point critical max along the segment (per unit t and per unit distance):')
for t in ('1e-6', '1e-5', '1e-4', '1e-3', '1e-2'):
    tt = mp.mpf(t)
    C = shifted(XS, tt, dn)
    cs = critical_set(C)
    g = max(v for v, *_ in cs)
    print('    t=%-7s  gamma - gamma* = %-16s  per-unit-t = %-14s  per-unit-dist = %s'
          % (t, mp.nstr(g - g0, 8), mp.nstr((g - g0) / tt, 8), mp.nstr((g - g0) / (tt * nd), 8)))

# ---- A4: SLSQP lambda audit ----------------------------------------------
from scipy.optimize import minimize as spmin
Jf = np.array([[float(x) for x in row] for row in J])
def obj(lam):
    r = Jf.T @ lam
    return float(r @ r)
best = None
for t in range(10):
    lam0 = np.random.default_rng(t).dirichlet(np.ones(18))
    o = spmin(obj, lam0, method='SLSQP', constraints=[{'type': 'eq', 'fun': lambda l: l.sum() - 1}],
              bounds=[(0, 1)] * 18, options={'maxiter': 8000, 'ftol': 1e-28})
    if best is None or o.fun < best.fun:
        best = o
lam = best.x
print('\nA4  SLSQP lambda: sum = %.16f  min = %.6e  ||J^T lam|| = %.6e'
      % (lam.sum(), lam.min(), np.linalg.norm(Jf.T @ lam)))
gd = np.array([float(x) for x in gdir])
print('    lam (J d)   = %.6e   <-- must be <= max_i (J d)_i = %.6e'
      % (float(lam @ (Jf @ np.array([float(x) for x in dn]))), float((Jf @ np.array([float(x) for x in dn])).max())))
print('    lam (direct) = %.6e   <-- must be <= max_i direct  = %.6e'
      % (float(lam @ gd), float(gd.max())))

json.dump({'dhat_max_fprime': mp.nstr(max(gdir), 12), 'dhat_min_fprime': mp.nstr(min(gdir), 12),
           'gdir': [mp.nstr(x, 12) for x in gdir], 'Jd': [mp.nstr(x, 12) for x in Jd],
           'lambda': lam.tolist(), 'lambda_sum': float(lam.sum()),
           'lambda_Jd': float(lam @ (Jf @ np.array([float(x) for x in dn])))},
          open(P / 'r20_direction_audit.json', 'w'), indent=2)
print('\nwritten r20_direction_audit.json')
