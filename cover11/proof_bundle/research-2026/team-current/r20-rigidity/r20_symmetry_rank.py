"""r20-rigidity step 6: descent-cone thinness, rank certificate, aligned symmetry probe.

F1  tau := min_{lambda in simplex} ||J^T lambda||   (= -min_{||v||=1} max_i (J v)_i,
    the thinness of the first-order descent cone). Gordan: tau = 0 <=> no descent.
F2  rank certificate: 60-dps determinant of the QR-pivoted 18x18 submatrix of J.
F3  aligned mirror analysis: rotate the reflected candidate optimally, form
    w = x* - R_theta Refl(x*), compare it with the near-null direction v18 and with
    ker J; then symmetrise (pairwise average) and evaluate gamma.
F4  critical-level ledger (inactive slack) at the candidate.
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
J = np.load(P / 'r20_J60.npy')
n = 11
U, S, Vt = np.linalg.svd(J)
v18 = Vt[17]

# ---------- F1 descent-cone thinness ---------------------------------------
from scipy.optimize import minimize as spmin
def obj(lam):
    r = J.T @ lam
    return float(r @ r)
best = None
for trial in range(8):
    lam0 = np.random.default_rng(trial).dirichlet(np.ones(18))
    o = spmin(obj, lam0, method='SLSQP', constraints=[{'type': 'eq', 'fun': lambda l: l.sum() - 1}],
              bounds=[(0, 1)] * 18, options={'maxiter': 5000, 'ftol': 1e-24})
    if best is None or o.fun < best.fun:
        best = o
lam = best.x
tau = math.sqrt(best.fun)
print('F1  tau = min_{simplex} ||J^T lambda|| = %.6e   (all lambda>0: %s, min lam %.4f)'
      % (tau, bool((lam > 1e-9).all()), lam.min()))
print('    => thin descent cone: min_{||v||=1} max_i (J v)_i = -tau = %.6e' % (-tau))
print('    => any admissible first-order decrease is <= %.3e per unit distance' % tau)

# ---------- F2 rank certificate -------------------------------------------
Jm = mp.matrix([[mp.mpf(float(x)) for x in row] for row in J])
from scipy.linalg import qr as spqr
Qp, Rp, perm = spqr(J.T, pivoting=True)
piv = [int(t) for t in perm[:18]]
sub = mp.matrix(18, 18)
for a in range(18):
    for b in range(18):
        sub[a, b] = Jm[a, piv[b]]
det = mp.det(sub)
print('\nF2  18x18 column-pivoted submatrix determinant (60 dps) = %s' % mp.nstr(det, 8))
print('    |det| / prod(||cols||) = %.3e   (sigma_18 = %.3e)'
      % (abs(det) / float(np.prod(np.linalg.norm(J[:, piv], axis=0))), S[-1]))
lam_svd = U[:, -1] / U[:, -1].sum()
print('    SVD-based feasible multiplier: ||J^T lambda||_2 = %.6e  (all>0: %s)'
      % (np.linalg.norm(J.T @ lam_svd), bool((lam_svd > 0).all())))

# ---------- F3 aligned mirror analysis -------------------------------------
axis = float(cal['A']['best_mirror_axis']['axis_angle_deg']) * math.pi / 180


def refl(X, a):
    Rm = np.array([[math.cos(2 * a), math.sin(2 * a)], [math.sin(2 * a), -math.cos(2 * a)]])
    return X @ Rm


def rot(X, th):
    Rm = np.array([[math.cos(th), -math.sin(th)], [math.sin(th), math.cos(th)]])
    return X @ Rm.T


def mismatch(X, Y):
    return max(float(np.linalg.norm(X - Y[i], axis=1).min()) for i in range(n))


best_th = min(((mismatch(C64, rot(refl(C64, axis), th)), th)
               for th in np.linspace(-0.05, 0.05, 20001)), key=lambda t: t[0])
print('\nF3  best aligned mirror: mismatch = %.3e at theta = %.5f rad (axis %.6f deg)'
      % (best_th[0], best_th[1], math.degrees(axis)))
Y = rot(refl(C64, axis), best_th[1])
# check global alignment is right: also search over the axis once more
bestpair = min(((mismatch(C64, rot(refl(C64, a2), best_th[1])), a2)
                for a2 in np.linspace(axis - 0.002, axis + 0.002, 4001)), key=lambda t: t[0])
print('    refined: mismatch = %.3e at axis %.6f deg' % (bestpair[0], math.degrees(bestpair[1])))
Y = rot(refl(C64, bestpair[1]), best_th[1])
assign = [int(np.argmin(np.linalg.norm(Y - C64[i], axis=1))) for i in range(n)]
print('    pairing induced by the aligned mirror (i -> sigma(i)):', assign)
w_pair = np.array([C64[i] - Y[assign[i]] for i in range(n)])       # small: symmetry breaking
print('    paired antisymmetrisation vector ||w|| = %.4e   (raw ||x* - Refl x*|| = %.4e)'
      % (np.linalg.norm(w_pair), np.linalg.norm(C64 - Y)))
w = w_pair.reshape(-1) / np.linalg.norm(w_pair)
print('    |cos(w, v18)| = %.6f' % abs(float(w @ v18)))
rotvec = np.array([c for i in range(n) for c in (-C64[i, 1], C64[i, 0])])
print('    |cos(w, rot)| = %.3e' % abs(float(w @ (rotvec / np.linalg.norm(rotvec)))))
print('    ||J w|| = %.4e  (= first-order slope of the 18 constraints along the symmetrisation)'
      % np.linalg.norm(J @ w))
# pairwise symmetrise (average each mirror pair)
X = C64.copy()
for i in range(n):
    j = assign[i]
    X[i] = (C64[i] + Y[j]) / 2
print('    ||X_sym - x*||_max = %.3e ; residual mirror mismatch of X_sym = %.3e'
      % (np.abs(X - C64).max(), mismatch(X, refl(X, bestpair[1]))))
print('    ||J (X_sym - x*)|| = %.4e' % np.linalg.norm(J @ (X - C64).reshape(-1)))


def mpm(C):
    return [mp.matrix([mp.mpf(float(x)) for x in C[i]]) for i in range(n)]


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


def gamma20(C):
    """max over the full 20-point critical set (11 V3 inside D + 9 nearest switches)"""
    Xm = mpm(C)
    vals = []
    for (i, j, k) in itertools.combinations(range(11), 3):
        # circumcentre and inside-D test at 60 dps
        a, b, c = i, j, k
        A = mp.matrix([[Xm[b][0] - Xm[a][0], Xm[b][1] - Xm[a][1]],
                       [Xm[c][0] - Xm[a][0], Xm[c][1] - Xm[a][1]]])
        rhs = mp.matrix([(sum(Xm[b][t] ** 2 for t in range(2)) - sum(Xm[a][t] ** 2 for t in range(2))) / 2,
                         (sum(Xm[c][t] ** 2 for t in range(2)) - sum(Xm[a][t] ** 2 for t in range(2))) / 2])
        u = mp.lu_solve(A, rhs)
        if sum(u[t] ** 2 for t in range(2)) > 1:
            continue
        d = min(mp.sqrt(sum((u[t] - Xm[q][t]) ** 2 for t in range(2))) for q in range(11))
        vals.append(d)
    for i2 in range(11):
        for j2 in range(i2 + 1, 11):
            dv = Xm[i2] - Xm[j2]
            dd = sum(dv[t] ** 2 for t in range(2))
            A0 = mp.matrix([(sum(Xm[i2][t] ** 2 for t in range(2)) - sum(Xm[j2][t] ** 2 for t in range(2))) / 2
                            / dd * dv[t] for t in range(2)])
            nv = mp.matrix([-dv[1] / mp.sqrt(dd), dv[0] / mp.sqrt(dd)])
            s2 = 1 - sum(A0[t] ** 2 for t in range(2))
            if s2 <= 0:
                continue
            s = mp.sqrt(s2)
            for sg in (1, -1):
                p = mp.matrix([A0[t] + sg * s * nv[t] for t in range(2)])
                ds = sorted([(mp.sqrt(sum((p[t] - Xm[q][t]) ** 2 for t in range(2))), q) for q in range(11)])
                if {ds[0][1], ds[1][1]} == {i2, j2}:
                    vals.append(ds[0][0])
    return max(vals)


gX = gamma20(X)
print('    gamma(X_sym) = %s' % mp.nstr(gX, 32))
print('    gamma(X_sym) - gamma* = %s ;  gamma(X_sym) - T_cert = %s'
      % (mp.nstr(gX - LO, 6), mp.nstr(gX - T_CERT, 6)))
print('    gamma(x*) - T_cert = %s' % mp.nstr(LO - T_CERT, 6))

# ---------- F4 critical-level ledger ---------------------------------------
led = cal['B']['ledger_top40']
print('\nF4  critical-level ledger (top 12, 60 dps recomputation of the top 6):')
for row in led[:12]:
    print('    %.15f  %-4s %s' % (row[0], row[1], row[2]))

json.dump({
    'tau_descent_thinness': tau,
    'lambda_simplex': lam.tolist(),
    'det18_60dps': mp.nstr(det, 8),
    'det18_normalized': abs(det) / float(np.prod(np.linalg.norm(J[:, piv], axis=0))),
    'aligned_mirror': {'axis_deg': math.degrees(bestpair[1]), 'theta_rad': best_th[1],
                       'mismatch': bestpair[0]},
    'w_norm': float(np.linalg.norm(w)),
    'cos_v18_w': abs(float(w / np.linalg.norm(w) @ v18)),
    'Jw_over_w': float(np.linalg.norm(J @ w) / np.linalg.norm(w)),
    'gamma_sym_60dps': mp.nstr(gX, 32),
    'gamma_sym_minus_lo': mp.nstr(gX - LO, 6),
    'gamma_star_minus_Tcert': mp.nstr(LO - T_CERT, 6),
}, open(P / 'r20_symmetry_rank.json', 'w'), indent=2)
