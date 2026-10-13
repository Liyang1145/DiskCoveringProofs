"""r20-rigidity step 3: precision probes around the saved n11 candidate.

Q1  Is the first-order (Gordan/Danskin) certificate EXACT or only ~2e-9?
      recompute J at 60 dps / h=1e-20 and compare with the 40 dps result.
Q2  Does a first-order descent direction exist at that 2e-9 level (i.e. is the
      stored object slightly improvable)?  evaluate gamma along +-v_min in mpmath.
Q3  Symmetry: the object is NOT exactly mirror symmetric (mismatch 3.5e-9).
      Symmetrise it onto the best mirror axis and compare gamma with
      C529 (saved object) and T_cert (registered 1e-60 symmetric witness).
Q4  Cross-object comparison: saved candidate vs n11/kkt2/frozen.json vs
      research-2026/session2/n11alg/cert_sym60.json.
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
LO = mp.mpf(raw['certified_interval']['lo'])
T_CERT = mp.mpf('0.379983853119838689722261606136093214308718957')
cal = json.loads((P / 'r20_calibration.json').read_text(encoding='utf-8'))
tight = cal['B']['tight_points']
axis = mp.mpf(cal['A']['best_mirror_axis']['axis_angle_deg']) * mp.pi / 180
n = 11


def mpm_exact(rawjson):
    return [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** 17 for v in a])
            for a in rawjson['centers_scaled_1e17']]


def mpm(C):
    return [mp.matrix([mp.mpf(float(x)) for x in C[i]]) for i in range(n)]


def shifted(Cbase, delta_flat):
    """add a float64 perturbation vector (flattened 22) to an mpmath centre list"""
    out = []
    for i in range(n):
        out.append(mp.matrix([Cbase[i][0] + mp.mpf(float(delta_flat[2 * i])),
                              Cbase[i][1] + mp.mpf(float(delta_flat[2 * i + 1]))]))
    return out


def circumcentre_mp(C, tri):
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


def dist(p, q):
    return mp.sqrt(sum((p[t] - q[t]) ** 2 for t in range(2)))


# structural lists fixed once (stable under tiny perturbations)
acts = []
for p in tight:
    if p['kind'] == 'V3':
        acts.append(('V3', tuple(p['sites']), None))
    else:
        pt = mp.matrix([mp.mpf(v) for v in p['point']])
        i, j = p['sites']
        dv = C64[i] - C64[j]
        dd = float(dv @ dv)
        A0 = (0.5 * (C64[i] @ C64[i] - C64[j] @ C64[j]) / dd) * dv
        nv = np.array([-dv[1], dv[0]]) / math.sqrt(dd)
        sgn = 1 if ((np.array(p['point']) - A0) @ nv) > 0 else -1
        acts.append(('V2b', (i, j), sgn))
assert len(acts) == 18


def f_of(kind, sites, sgn, C, h=None):
    if kind == 'V3':
        u = circumcentre_mp(C, sites)
        return dist(u, C[sites[0]])
    p = boundary_point(C, sites[0], sites[1], sgn)
    return dist(p, C[sites[0]])


def gamma_fixed(C):
    return max(f_of(k, s, g, C) for (k, s, g) in acts)


CM = mpm_exact(raw)
print('gamma(x*) at 60 dps =', mp.nstr(gamma_fixed(CM), 32))
print('certified lo        =', mp.nstr(LO, 32))
print('gamma - lo          =', mp.nstr(gamma_fixed(CM) - LO, 6))
print('T_cert              =', mp.nstr(T_CERT, 32), ' (C529 - T_cert =',
      mp.nstr(LO - T_CERT, 6), ')')

# ---------- Q1: J at higher precision --------------------------------------
def build_J(h, dps):
    mp.mp.dps = dps
    C = mpm_exact(raw)
    J = np.zeros((18, 22))
    for a, (kind, sites, sgn) in enumerate(acts):
        for k in range(n):
            for t in range(2):
                Cp = [mp.matrix(C[i]) for i in range(n)]
                Cp[k][t] += h
                Cq = [mp.matrix(C[i]) for i in range(n)]
                Cq[k][t] -= h
                J[a, 2 * k + t] = float((f_of(kind, sites, sgn, Cp) - f_of(kind, sites, sgn, Cq)) / (2 * h))
    return J


J40 = build_J(mp.mpf('1e-14'), 40)
J60 = build_J(mp.mpf('1e-20'), 60)
print('\nQ1  max |J(h=1e-14,40dps) - J(h=1e-20,60dps)| = %.3e' % np.abs(J40 - J60).max())
for tag, Jm in (('h=1e-14/40dps', J40), ('h=1e-20/60dps', J60)):
    U, S, Vt = np.linalg.svd(Jm)
    ul = U[:, -1]
    print('   %-14s sigma_min = %.6e   next = %.6e   left-null sign pattern: %s (min %.3e)'
          % (tag, S[-1], S[-2], ''.join('+' if x > 0 else '-' for x in ul), ul.min()))
np.save(P / 'r20_J60.npy', J60)

U, S, Vt = np.linalg.svd(J60)
vmin = Vt[-1]
print('\nQ2  right singular vector for sigma_min: ||J v|| = %.3e' % np.linalg.norm(J60 @ vmin))
print('    J v components (should be ~ sigma*u, u>0): min %.3e max %.3e'
      % ((J60 @ vmin).min(), (J60 @ vmin).max()))
Cm = mpm(C64)
print('    gamma along +-t v_min (mpmath 60 dps):')
g0 = gamma_fixed(CM)
for t in ('1e-9', '2e-9', '5e-9', '1e-8', '5e-8', '2e-7', '1e-6'):
    tt = mp.mpf(t)
    Cp = shifted(CM, float(tt) * vmin)
    Cq = shifted(CM, -float(tt) * vmin)
    dp = gamma_fixed(Cp) - g0
    dq = gamma_fixed(Cq) - g0
    print('       t=%-6s  +: %+.6e     -: %+.6e' % (t, dp, dq))

# ---------- Q3: symmetrisation ---------------------------------------------
Rm = np.array([[math.cos(2 * float(axis)), math.sin(2 * float(axis))],
               [math.sin(2 * float(axis)), -math.cos(2 * float(axis))]])
Cr = C64 @ Rm
X = C64.copy()
for i in range(n):
    j = int(np.argmin(np.linalg.norm(C64 - Cr[i], axis=1)))
    if j == i:
        X[i] = (C64[i] + Cr[i]) / 2          # on-axis site -> project onto the axis
    elif int(np.argmin(np.linalg.norm(C64 - Cr[j], axis=1))) == i:
        X[i] = (C64[i] + Cr[j]) / 2          # pair -> average
        X[j] = X[i]
    else:
        X[i] = (C64[i] + Cr[j]) / 2
print('\nQ3  symmetrised configuration:')
print('    max shift |X - x*| = %.3e' % np.abs(X - C64).max())
# verify invariance
Xr = X @ Rm
mm = max(float(np.linalg.norm(X - Xr[i], axis=1).min()) for i in range(n))
print('    residual mirror mismatch of X = %.3e' % mm)
gX = gamma_fixed(mpm(X))
print('    gamma(X_sym)      =', mp.nstr(gX, 32))
print('    gamma(X_sym) - lo =', mp.nstr(gX - LO, 6))
print('    gamma(X_sym) - T_cert =', mp.nstr(gX - T_CERT, 6))

# antisymmetrisation direction
w = (C64 - Cr).reshape(-1)
w = w / np.linalg.norm(w)
print('\n    |cos(v_min, antisymmetrisation direction)| = %.6f' % abs(float(vmin @ w)))

# ---------- Q4: other objects ----------------------------------------------
def report_object(path, key='centers_scaled_1e17', scale=1e17):
    p = ROOT / path
    if not p.exists():
        print('   %s : MISSING' % path)
        return
    d = json.loads(p.read_text(encoding='utf-8-sig'))
    if key in d:
        Cx = np.array([[int(v) / scale for v in a] for a in d[key]])
    elif 'centers' in d:
        Cx = np.array(d['centers'], dtype=float)
    else:
        print('   %s : no centres key; keys = %s' % (path, list(d.keys())[:12]))
        return
    gx = gamma_fixed(mpm(Cx))
    # best mirror axis by simple scan
    def mm_(a):
        R2 = np.array([[math.cos(2 * a), math.sin(2 * a)], [math.sin(2 * a), -math.cos(2 * a)]])
        C2 = Cx @ R2
        return max(float(np.linalg.norm(Cx - C2[i], axis=1).min()) for i in range(len(Cx)))
    best = min((mm_(a), a) for a in np.linspace(-math.pi, math.pi, 72001))
    print('   %-52s gamma=%s  mirror mismatch=%.3e at %.4f deg'
          % (path, mp.nstr(gx, 22), best[0], math.degrees(best[1])))
    return Cx


print('\nQ4  other candidate objects:')
report_object('n11/upper/certified_object.json')
report_object('n11/kkt2/frozen.json')
report_object('research-2026/session2/n11alg/cert_sym60.json')
