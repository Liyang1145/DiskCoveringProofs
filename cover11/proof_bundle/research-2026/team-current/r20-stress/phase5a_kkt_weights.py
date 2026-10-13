"""Phase 5a: physical covering KKT in the angle model at the exact TC chart point.

Correct object (per lead): R_shape = max_f b_f is NONSMOOTH at the 18-branch tie; there is no
ordinary gradient. Stationarity is  0 in dR_shape + N_M, equivalently the linear system
    sum_{f in A} lam_f grad b_f  +  J8^T mu = 0 ,   lam >= 0, sum lam = 1
i.e. (after eliminating mu)   M lam = 0  with  M = (I - P_row) W_A^T  (29 x 18).
No Newton, no ordinary-gradient claims. Reports:
  (1) the system and its SVD;
  (2) numeric feasible positive weights on the simplex (at the exact TC chart point);
  (3) mirror averaging -> orbit weights;
  (4) chart projection of the model KKT and the lift test against the TC multipliers.
Writes only in r20-stress/out .
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp
from scipy.optimize import minimize

import mp_model_r20 as MM

W_DIR = Path(__file__).parent; OUT = W_DIR / 'out'
LEAD = W_DIR.parent / 'lead'
mp.mp.dps = 50

M0 = MM.load()
ns, shape, Nr, a0 = M0['ns'], M0['shape'], M0['Nr'], M0['a0']
faces = [list(f) for f in ns['faces']]
D = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())
root = [mp.mpf(s) for s in D['numeric_root']]
a04r, y0r, y1r, Rr, lam_TC = root[:4], root[4], root[5], root[6], root[7:]


def tc_geo(u):
    a04 = [mp.mpf(float(v)) for v in u[:4]]
    y0, y1, R = mp.mpf(float(u[4])), mp.mpf(float(u[5])), mp.mpf(float(u[6]))
    a4 = mp.pi - 2 * sum(a04)
    a = [a04[0], a04[1], a04[2], a04[3], a4, a04[3], a04[2], a04[1], a04[0]]
    rho = [mp.cos(a[k]) - mp.sqrt(R * R - mp.sin(a[k]) ** 2) for k in range(9)]
    th = [mp.mpf(0)] * 9
    for k in range(5, 9):
        th[k] = th[k - 1] + a[k - 1] + a[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (a[k] + a[k + 1])
    C = [(rho[k] * mp.cos(th[k]), rho[k] * mp.sin(th[k])) for k in range(9)]
    U = [(C[k][0] + C[(k + 1) % 9][0] - mp.cos(th[k] + a[k]), C[k][1] + C[(k + 1) % 9][1] - mp.sin(th[k] + a[k]))
         for k in range(9)]
    m_, d_ = (y0 + y1) / 2, (y1 - y0) / 2
    return a, C, [(y0, mp.mpf(0)), (y1, mp.mpf(0))], U, (m_, mp.sqrt(R * R - d_ * d_)), R


def res5(u):
    a, C, hubs, U, waist, R = tc_geo(u)
    dist = lambda p, q: mp.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)
    out = [dist(U[k], hubs[l]) - R for (k, l) in [(1, 1), (2, 0), (3, 0), (8, 1)]]
    out.append(dist(waist, C[6]) - R)
    return out


def angle_vector(u):
    a, C, hubs, U, waist, R = tc_geo(u)
    pts = {((6 - k) % 9): C[k] for k in range(9)}
    pts[9], pts[10] = hubs[0], hubs[1]
    ang = []
    for f in faces:
        for j in range(3):
            p = pts[f[j]]; q = pts[f[(j + 1) % 3]]; r = pts[f[(j + 2) % 3]]
            v1 = (q[0] - p[0], q[1] - p[1]); v2 = (r[0] - p[0], r[1] - p[1])
            ang.append(float(mp.atan2(abs(v1[0] * v2[1] - v1[1] * v2[0]), v1[0] * v2[0] + v1[1] * v2[1])))
    for s in range(9):
        i = (5 - s) % 9
        ang.append(float(mp.asin(mp.sqrt((C[i][0] - C[(i + 1) % 9][0]) ** 2 + (C[i][1] - C[(i + 1) % 9][1]) ** 2) / (2 * R))))
    return np.array(ang)


u0 = np.array([float(v) for v in root[:7]])
a_TC = angle_vector(u0)
y_TC = np.linalg.pinv(Nr) @ (a_TC - a0)
print('[point] exact TC chart point: |y_TC| = %.3e ; a_TC vs saved a0: %.3e' % (np.linalg.norm(y_TC), np.abs(a_TC - a0).max()))

# ---------------- Jacobian at a_TC (50 digit) --------------------------------------------
bc = MM.make_mp_model(dict(M0, a0=a0 + Nr @ y_TC))
G = np.array([[float(x) for x in row] for row in MM.jac_mp(bc)])
J8, W = G[20:], G[:20]
bvals = np.array([float(x) for x in bc([mp.mpf(0)] * 29)[0]])
u_norm = np.exp(bvals - bvals.max())
act = np.where(u_norm > 1 - 1e-12)[0]
print('[ties] branch spread max-min = %.3e ; active (u>1-1e-12) = %d ; slack u = %s'
      % (bvals.max() - bvals.min(), len(act),
         [round(float(u_norm[i]), 9) for i in range(20) if u_norm[i] <= 1 - 1e-12]))
assert len(act) == 18

# ---------------- (1) the system --------------------------------------------------------
Jg = W[act]                                    # 18 x 29
Prow = J8.T @ np.linalg.inv(J8 @ J8.T) @ J8
Mmat = (np.eye(29) - Prow) @ Jg.T              # 29 x 18 ; condition: Mmat @ lam = 0
svM = np.linalg.svd(Mmat, compute_uv=False)
print('[system] M = P_tangent * W_A^T is 29x18 ; sv min-3 =', np.array2string(svM[-3:], precision=4),
      ' ; rank =', int((svM > 1e-9).sum()))
print('         ||M lam_TC-idea|| not applicable (lam_TC acts on the 5 contacts, not the 18 branches)')

# ---------------- (2) feasible positive weights ------------------------------------------
def ls(x0):
    return minimize(lambda l: float(np.linalg.norm(Mmat @ l) ** 2), x0, method='SLSQP',
                    constraints=[{'type': 'eq', 'fun': lambda l: l.sum() - 1.0}],
                    bounds=[(0.0, 1.0)] * 18, options={'maxiter': 2000, 'ftol': 1e-24})
o1, o2 = ls(np.ones(18) / 18), ls(np.full(18, 0.05))
best = o1.x if np.linalg.norm(Mmat @ o1.x) <= np.linalg.norm(Mmat @ o2.x) else o2.x
res = float(np.linalg.norm(Mmat @ best))
mu = -np.linalg.solve(J8 @ J8.T, J8 @ (Jg.T @ best))
print('[weights] LS on simplex: ||M lam|| = %.3e ; min lam = %.6e ; sum = %.15f ; ||Jg^T lam + J8^T mu||inf = %.3e'
      % (res, best.min(), best.sum(), float(np.abs(Jg.T @ best + J8.T @ mu).max())))
print('          lam (18) =', np.array2string(best, precision=6, max_line_width=200))

# ---------------- (3) mirror averaging -> orbit weights ----------------------------------
sig = lambda s: ((4 - s) % 9) if s < 9 else s
pi_face = {}
for t, f in enumerate(faces):
    ft = sorted([sig(v) for v in f])
    pi_face[t] = next(i for i, g in enumerate(faces) if sorted(g) == ft)
pi = np.array([pi_face[t] for t in range(11)] + [((3 - i) % 9) + 11 for i in range(9)])   # factor permutation
print('[mirror] factor permutation on the 20 factors:', pi.tolist())
pos = {int(f): i for i, f in enumerate(act)}
assert all(int(pi[f]) in pos for f in act), 'active set not sigma-invariant'
Pact = np.array([pos[int(pi[f])] for f in act])
lam_sym = 0.5 * (best + best[Pact])
print('[mirror] ||M lam_sym|| = %.3e ; min = %.6e ; ||lam_sym - lam_saved_style||inf = %.3e'
      % (float(np.linalg.norm(Mmat @ lam_sym)), lam_sym.min(), float(np.abs(lam_sym - best).max())))
orbits, seen = [], set()
for i in range(18):
    if i not in seen:
        j = int(Pact[i]); seen.add(i); seen.add(j)
        orbits.append([i, j] if j != i else [i])
print('[mirror] orbits of the active set: %d' % len(orbits), orbits)
print('[mirror] orbit weights (lam_f per orbit):', [round(float(lam_sym[o[0]]), 6) for o in orbits])

# ---------------- (4) chart projection + lift test ---------------------------------------
pinvNr = np.linalg.pinv(Nr)


def bf_on_chart(u, f):
    """b_f composed with the TC chart map (in the chart parameter u)."""
    y = pinvNr @ (angle_vector(u) - a_TC)
    return float(bc([mp.mpf(float(x)) for x in y])[0][f])


def chart_deriv(fun, k, h=1e-7):
    up = u0.copy(); um = u0.copy(); up[k] += h; um[k] -= h
    return (fun(up) - fun(um)) / (2 * h)


Gb = np.array([[chart_deriv(lambda uu, f=f: bf_on_chart(uu, f), k) for k in range(7)] for f in act])  # 18x7
Gf = np.array([[chart_deriv(lambda uu, i=i: float(res5(uu)[i]), k) for k in range(7)] for i in range(5)])  # 5x7
# boundary arc-endpoint constraints: |P_k(s) - C_k| - R along the chart (saturation => identically 0)
def bnd_val(u, k, s):
    a, C, hubs, U, waist, R = tc_geo(u)
    P = (mp.cos(0) * 0 + mp.cos(0), mp.mpf(0))
    P = (mp.cos(0), mp.sin(0))
    return None
print('[chart] d(b_f)/du : 18x7, sv =', np.array2string(np.linalg.svd(Gb, compute_uv=False), precision=4))
print('[chart] rank(Gb) = %d' % int((np.linalg.svd(Gb, compute_uv=False) > 1e-6).sum()))
lamT = np.array([float(v) for v in lam_TC])
print('[chart] model KKT projected on the chart: max|Gb^T lam_sym| = %.3e (=> 0 in subgradient sense)'
      % float(np.abs(Gb.T @ lam_sym).max()))
print('[chart] TC system: |Gf^T lam_TC - e_R|inf = %.3e'
      % float(np.abs(Gf.T @ lamT - np.array([0, 0, 0, 0, 0, 0, 1.0])).max()))
# lift: express the 5 contact differentials through the 18 branch differentials (if possible)
Yt = np.linalg.lstsq(Gb.T, Gf.T, rcond=None)[0]        # 18 x 5
Yfit = Gb.T @ Yt                                       # 7 x 5 = predicted Gf^T
print('[lift] fit Gf^T ~ Gb^T Yt : residual = %.3e (relative %.3e)'
      % (float(np.abs(Yfit - Gf.T).max()), float(np.abs(Yfit - Gf.T).max() / np.abs(Gf.T).max())))
print('[lift] TC multipliers lam_TC =', np.array2string(lamT, precision=6),
      ' ; their branch-avatar Yt @ lam_TC =', np.array2string(Yt @ lamT, precision=6))
print('[lift] branch-avatar sum = %.6f (model weights sum to 1)' % float((Yt @ lamT).sum()))

out = dict(scope='physical covering KKT at the exact TC chart point: weights, mirror orbits, chart projection, lift test; numeric',
           point=dict(y_norm=float(np.linalg.norm(y_TC)), dev_from_a0=float(np.abs(a_TC - a0).max()),
                      tie_spread=float(bvals.max() - bvals.min()), n_active=int(len(act)), act=act.tolist()),
           system=dict(sv_M=svM.tolist(), rank=int((svM > 1e-9).sum())),
           weights=dict(lam=best.tolist(), res=res, mu=mu.tolist(),
                        full_res_inf=float(np.abs(Jg.T @ best + J8.T @ mu).max())),
           mirror=dict(pi=pi.tolist(), orbits=orbits, lam_sym=lam_sym.tolist(),
                       res_sym=float(np.linalg.norm(Mmat @ lam_sym)),
                       orbit_weights=[float(lam_sym[o[0]]) for o in orbits]),
           chart=dict(Gb_sv=np.linalg.svd(Gb, compute_uv=False).tolist(),
                      model_KKT_projected=float(np.abs(Gb.T @ lam_sym).max()),
                      TC_residual=float(np.abs(Gf.T @ lamT - np.array([0, 0, 0, 0, 0, 0, 1.0])).max())),
           lift=dict(Yt=Yt.tolist(), fit_residual=float(np.abs(Yfit - Gf.T).max()),
                     fit_rel=float(np.abs(Yfit - Gf.T).max() / np.abs(Gf.T).max()),
                     branch_avatar=(Yt @ lamT).tolist(), lam_TC=lamT.tolist(),
                     avatar_sum=float((Yt @ lamT).sum())))
(OUT / 'phase5a_kkt_weights.json').write_text(json.dumps(out, indent=2))
print('[done] -> out/phase5a_kkt_weights.json')
