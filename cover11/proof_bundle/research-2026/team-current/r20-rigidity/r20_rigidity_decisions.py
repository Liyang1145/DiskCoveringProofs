"""r20-rigidity continuation (step 9): the decidable local-rigidity statements.

Compares  x* = n11/upper/certified_object.json (22 ints/1e17, saved certified UB)
with     X60 = research-2026/session2/n11alg/cert_sym60.json (22 ints/1e60, registered
         symmetric ideal, RD_interval lo = R_stru).

Decidable questions answered here (numeric-to-1e-40, exact rational inputs, 80 dps):
  Q1  are the two objects the same configuration up to a rotation?  (optimal axis + residual)
  Q2  at X60: is the 18x22 active Jacobian J18 of FULL ROW RANK, and is there a strictly
      positive multiplier u with u^T J18 = 0 (Danskin stationarity 0 in ri conv grad f_i)?
      -> this is the "local unique root vs local optimum" separation.
  Q3  at x*: same two questions (rank / Gordan residual) and the descent slope bound.
  Q4  the maximal-minor determinant test (re-audit of the earlier F2 claim "det = 0").
  Q5  gamma along the segment from x* toward the aligned X60: initial slope.

All outputs numeric diagnosis (no registered claim). Writes r20_rigidity_decisions.json.
"""
import json, math, itertools
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


# ------------------------------------------------------------------ geometry
def circ(C, tri):
    a, b, c = tri
    A = mp.matrix([[C[b][0] - C[a][0], C[b][1] - C[a][1]],
                   [C[c][0] - C[a][0], C[c][1] - C[a][1]]])
    rhs = mp.matrix([(sum(C[b][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2,
                     (sum(C[c][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2])
    return mp.lu_solve(A, rhs)


def bis_bd(C, i, j, sgn):
    dv = C[i] - C[j]
    dd = sum(dv[t] ** 2 for t in range(2))
    A0 = mp.matrix([(sum(C[i][t] ** 2 for t in range(2)) - sum(C[j][t] ** 2 for t in range(2))) / 2
                    / dd * dv[t] for t in range(2)])
    nv = mp.matrix([-dv[1] / mp.sqrt(dd), dv[0] / mp.sqrt(dd)])
    s2 = 1 - sum(A0[t] ** 2 for t in range(2))
    if s2 <= 0:
        return None
    return mp.matrix([A0[t] + sgn * mp.sqrt(s2) * nv[t] for t in range(2)])


def dd(p, q):
    return mp.sqrt(sum((p[t] - q[t]) ** 2 for t in range(2)))


def critical_set(C):
    crit, allp = [], []
    for tri in itertools.combinations(range(N), 3):
        u = circ(C, tri)
        if u is None or sum(u[t] ** 2 for t in range(2)) > 1:
            continue
        ds = sorted((dd(u, C[q]), q) for q in range(N))
        rec = {'kind': 'V3', 'sites': list(tri), 'f': (lambda CC, s=tri: dd(circ(CC, s), CC[s[0]]))}
        allp.append((ds[0][0], rec, set(q for _, q in ds[:3]) == set(tri)))
    for i, j in itertools.combinations(range(N), 2):
        for sgn in (1, -1):
            p = bis_bd(C, i, j, sgn)
            if p is None:
                continue
            ds = sorted((dd(p, C[q]), q) for q in range(N))
            rec = {'kind': 'V2b', 'sites': [i, j], 'sgn': sgn,
                   'f': (lambda CC, a=i, b=j, g=sgn: dd(bis_bd(CC, a, b, g), CC[a]))}
            allp.append((ds[0][0], rec, set(q for _, q in ds[:2]) == {i, j}))
    for val, rec, isc in allp:
        if isc:
            crit.append((val, rec))
    return crit, allp


def gamma(C, crit):
    return max(f(CC=C) if False else rec['f'](C) for _, rec in crit)


def grad16(rec, C, h=mp.mpf('1e-25')):
    """central-difference gradient (22,) at 80 dps"""
    g = []
    for i in range(N):
        for t in range(2):
            Cp = [mp.matrix(C[k]) for k in range(N)]
            Cm = [mp.matrix(C[k]) for k in range(N)]
            Cp[i][t] += h
            Cm[i][t] -= h
            g.append((rec['f'](Cp) - rec['f'](Cm)) / (2 * h))
    return g


def J18(C, crit):
    rows = [grad16(rec, C) for _, rec in crit]
    return mp.matrix(rows)


def report_J(J, label):
    m = J * J.T
    ev = mp.eigsy(m, eigvals_only=True)
    ev_sorted = sorted(ev, reverse=True)
    sig = [mp.sqrt(max(e, mp.mpf(0))) for e in ev_sorted]
    out = {'label': label, 'singular_values': [mp.nstr(s, 12) for s in sig],
           'sigma_min': mp.nstr(sig[-1], 12), 'sigma_2nd_min': mp.nstr(sig[-2], 12)}
    return out, sig


print('=== Q1  x* vs X60: rigid alignment (rotation only) ===')
th_best, m_best = None, mp.inf
for k in range(0, 2000):
    th = 2 * mp.pi * k / 2000
    Rm = mp.matrix([[mp.cos(th), -mp.sin(th)], [mp.sin(th), mp.cos(th)]])
    worst = mp.mpf(0)
    for i in range(N):
        p = Rm * X60[i]
        worst = max(worst, min(dd(p, XS[j]) for j in range(N)))
    if worst < m_best:
        m_best, th_best = worst, th
print('  coarse: axis = %s deg, mismatch = %s' % (mp.nstr(th_best * 180 / mp.pi, 8), mp.nstr(m_best, 6)))
for scale in ('1e-3', '1e-5', '1e-7', '1e-9', '1e-11'):
    sc = mp.mpf(scale)
    cur = th_best
    for k in range(-50, 51):
        th = cur + sc * mp.pi * k / 50
        Rm = mp.matrix([[mp.cos(th), -mp.sin(th)], [mp.sin(th), mp.cos(th)]])
        worst = mp.mpf(0)
        for i in range(N):
            p = Rm * X60[i]
            worst = max(worst, min(dd(p, XS[j]) for j in range(N)))
        if worst < m_best:
            m_best, th_best = worst, th
print('  refined: axis = %s deg, mismatch = %s' % (mp.nstr(th_best * 180 / mp.pi, 12), mp.nstr(m_best, 10)))
Rm = mp.matrix([[mp.cos(th_best), -mp.sin(th_best)], [mp.sin(th_best), mp.cos(th_best)]])
X60r = [Rm * X60[i] for i in range(N)]
perm = [int(min(range(N), key=lambda j: dd(X60r[i], XS[j]))) for i in range(N)]
print('  X60 (i) -> x* (j):', perm)
dev = [mp.nstr(dd(X60r[i], XS[perm[i]]), 6) for i in range(N)]
print('  per-site deviation after alignment:', dev)
# rotation-only distance between the shapes
print('  max deviation = %s' % mp.nstr(max(dd(X60r[i], XS[perm[i]]) for i in range(N)), 8))

print('\n=== Q2  X60: active set, J18, rank, Gordan ===')
crit60, all60 = critical_set(X60)
g60 = max(v for v, _ in crit60)
tight60 = [(v, r) for v, r in crit60 if v > g60 - mp.mpf('1e-9')]
print('  #critical = %d  #tight = %d  gap to next level = %s'
      % (len(crit60), len(tight60), mp.nstr(sorted([v for v, _ in crit60], reverse=True)[len(tight60)] - g60, 6)))
print('  spread of the 18 tight values = %s' % mp.nstr(max(v for v, _ in tight60) - min(v for v, _ in tight60), 6))
J60 = J18(X60, tight60)
r60, sig60 = report_J(J60, 'J18(X60)')
print('  sigma of J18(X60): min = %s  next = %s' % (r60['sigma_min'], r60['sigma_2nd_min']))
print('  sigma list:', r60['singular_values'])
# left-null (smallest singular) vector, sign pattern, and the exact residual u^T J
def npmat(J):
    return np.array([[float(J[i, j]) for j in range(J.cols)] for i in range(J.rows)])


U, S, Vt = np.linalg.svd(npmat(J60))
u = U[:, -1]
u = u / u.sum()
res = mp.matrix([sum(mp.mpf(float(u[i])) * J60[i, k] for i in range(18)) for k in range(22)])
print('  float64 left-null u sign pattern: %s   min=%.4e' % (''.join('+' if x > 0 else '-' for x in u), u.min()))
print('  || u^T J ||_inf (80 dps) = %s' % mp.nstr(max(abs(x) for x in res), 6))
# is the reported sigma_min exactly 0 or just tiny? recompute the Gram spectrum higher up
mp.mp.dps = 120
J60_120 = J18(X60, tight60)
ev = sorted(mp.eigsy(J60_120 * J60_120.T, eigvals_only=True), reverse=True)
print('  at 120 dps: sigma_min^2 = %s   sigma_2ndmin^2 = %s' % (mp.nstr(ev[-1], 6), mp.nstr(ev[-2], 6)))
mp.mp.dps = DPS
# mirror antisymmetrisation direction at X60 -> check it is in ker J60
axis60 = mp.mpf(0)
best60 = (mp.inf, None)
for k in range(1200):
    aa = 2 * mp.pi * k / 1200
    Rmm = mp.matrix([[mp.cos(2 * aa), mp.sin(2 * aa)], [mp.sin(2 * aa), -mp.cos(2 * aa)]])
    worst = mp.mpf(0)
    for i in range(N):
        p = Rmm * X60[i]
        worst = max(worst, min(dd(p, X60[j]) for j in range(N)))
    if worst < best60[0]:
        best60 = (worst, aa)
axis60 = best60[1]
Rmm = mp.matrix([[mp.cos(2 * axis60), mp.sin(2 * axis60)], [mp.sin(2 * axis60), -mp.cos(2 * axis60)]])
pairing = [int(min(range(N), key=lambda j: dd(Rmm * X60[i], X60[j]))) for i in range(N)]
w60 = []
for i in range(N):
    tgt = X60[pairing[i]]
    w60.append((X60[i][0] - tgt[0]) / 2)
    w60.append((X60[i][1] - tgt[1]) / 2)
nw = mp.sqrt(sum(x ** 2 for x in w60))
print('  X60 mirror axis %.9f deg, pairing %s' % (float(axis60 * 90 / mp.pi * 2), pairing))
print('  antisymmetrisation vector |w| = %s ;  |J60 w|_inf = %s'
      % (mp.nstr(nw, 6), mp.nstr(max(abs(sum(J60[i, k] * w60[k] for k in range(22))) for i in range(18)), 6)))
r60.update({'u_sign': ''.join('+' if x > 0 else '-' for x in u), 'u_min': float(u.min()),
            'uJ_inf': mp.nstr(max(abs(x) for x in res), 6),
            'sigma_min2_at120dps': mp.nstr(ev[-1], 6),
            'mirror_axis_deg': mp.nstr(axis60 * 180 / mp.pi, 10), 'pairing': pairing,
            'antisym_norm': mp.nstr(nw, 6),
            'Jw_inf': mp.nstr(max(abs(sum(J60[i, k] * w60[k] for k in range(22))) for i in range(18)), 6)})

print('\n=== Q3  x*: active set, J18, rank, Gordan ===')
critxs, allxs = critical_set(XS)
gxs = max(v for v, _ in critxs)
tightxs = [(v, r) for v, r in critxs if v > gxs - mp.mpf('1e-9')]
print('  #critical = %d  #tight = %d' % (len(critxs), len(tightxs)))
Jxs = J18(XS, tightxs)
rxs, sigxs = report_J(Jxs, 'J18(x*)')
print('  sigma of J18(x*): min = %s  next = %s' % (rxs['sigma_min'], rxs['sigma_2nd_min']))
Ux, Sx, Vtx = np.linalg.svd(npmat(Jxs))
ux = Ux[:, -1]
print('  float64 left-null u sign pattern: %s   min=%.4e  max=%.4e'
      % (''.join('+' if x > 0 else '-' for x in ux), ux.min(), ux.max()))
# certified-style check: is there a NONNEGATIVE (or strictly positive) multiplier with small residual?
from scipy.optimize import minimize as spmin
Jf = npmat(Jxs)
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
rr = Jf.T @ lam
print('  min_simplex ||J^T lam|| = %.6e   (all lam > 0: %s, min lam %.5f)'
      % (np.linalg.norm(rr), bool((lam > 1e-12).all()), lam.min()))
print('  => best first-order decrease slope on the 18 active rows = %.6e' % (-np.linalg.norm(rr)))
rxs.update({'gordan_residual': float(np.linalg.norm(rr)), 'lambda': lam.tolist()})

print('\n=== Q4  maximal-minor determinant audit ===')
for lab, J in (('x*', Jxs), ('X60', J60)):
    print('  %s: |det J[:,0:18]| (80 dps) = %s' % (lab, mp.nstr(abs(mp.det(J[:, 0:18])), 8)))
    print('      |det J[:,4:22]| (80 dps) = %s' % mp.nstr(abs(mp.det(J[:, 4:22])), 8))
    # best conditioned minor over all 22 choose 18 = 7315 column subsets is unnecessary:
    # the rank test that matters is the spectrum of J J^T, reported in Q2/Q3.

print('\n=== Q5  gamma along the segment x* -> aligned X60 ===')
# direction from x* to the aligned ideal, after the correspondence
dvec = []
for i in range(N):
    for t in range(2):
        dvec.append(X60r[perm.index(i)][t] - XS[i][t])
nd = mp.sqrt(sum(x ** 2 for x in dvec))
print('  |d| = %s  (max component %s)' % (mp.nstr(nd, 8), mp.nstr(max(abs(x) for x in dvec), 8)))
for t in ('1e-3', '1e-2', '3e-2', '1e-1', '3e-1', '1e0'):
    tt = mp.mpf(t)
    C = [mp.matrix([XS[i][0] + tt * dvec[2 * i], XS[i][1] + tt * dvec[2 * i + 1]]) for i in range(N)]
    critc, _ = critical_set(C)
    g = max(v for v, _ in critc)
    print('   t=%-5s  gamma(x*+t d) - gamma(x*) = %s' % (t, mp.nstr(g - gxs, 8)))

json.dump({'Q1': {'axis_deg': mp.nstr(th_best * 180 / mp.pi, 12), 'mismatch': mp.nstr(m_best, 10),
                  'perm': perm, 'max_dev': mp.nstr(max(dd(X60r[i], XS[perm[i]]) for i in range(N)), 8)},
           'Q2': r60, 'Q3': rxs,
           'gamma': {'x*': mp.nstr(gxs, 40), 'X60': mp.nstr(g60, 40)}},
          open(P / 'r20_rigidity_decisions.json', 'w'), indent=2)
print('\nwritten r20_rigidity_decisions.json')
