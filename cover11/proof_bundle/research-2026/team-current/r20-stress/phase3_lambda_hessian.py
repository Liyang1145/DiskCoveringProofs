"""Phase 3 (lead stage-3), corrected version.

(0) calibration / point-quality
(1) 50-digit Jacobian at the saved candidate a0
(2) λ-uniqueness: solve M λ = 0 on the simplex, M = P_tangent · (∇b_f)_{f∈A}
(3) point-accuracy diagnostic: Gauss-Newton refinement of the POINT (λ fixed, λ is NOT
    re-optimised) so that the stationarity defect M(y)λ vanishes; this separates
    "a0 is ~1e-9 off the exact candidate" from "no sharp stationary λ exists".
(4) CORRECT reduced Hessian of Φ_λ on the true manifold:
        H_L = H_Φ + Σ_j μ8_j H_{c8_j}      (normal correction, previously missing)
        H_red = Z^T H_L Z ,  Z = ker J8 (29x21)
    reported together with the old (void) Z^T H_Φ Z.
(5) one explicit negative tangential direction + reprojection/step-halving ladder.

Writes only inside research-2026/team-current/r20-stress/.
"""
import os, json, math, time
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp
from scipy.linalg import null_space, pinv
from scipy.optimize import minimize

import mp_model_r20 as MM

W_DIR = Path(__file__).parent; OUT = W_DIR / 'out'
T0 = time.time(); mp.mp.dps = 50

M = MM.load()
ns, shape, Nr, a0 = M['ns'], M['shape'], M['Nr'], M['a0']
lam_saved, mu_saved, act = np.asarray(M['lam']), np.asarray(M['mu']), np.asarray(M['act'])
bc = MM.make_mp_model(M)
Tcert_str = '0.3799838531198386897222616061360932143087189561522153170163892'
C529_str = '0.379983853119838709048518179573429853811597902801556119905385'
log_Tcert = float(mp.log(mp.mpf(Tcert_str)))
lam18 = lam_saved.copy()                      # the lead's λ, 18 entries aligned with act

# ---------------- float64 model pieces ----------------------------------------------------
def f64_bc(y):
    a = a0 + Nr @ y
    r, con, d = shape(a)
    return d['logg'] + math.log(max(d['rat'][0], 1e-100)), con[13:21], float(r), con, d, a

def f64_jac(y, h=1e-5):
    n = 29
    def col(s):
        bp, cp, *_ = f64_bc(y + s * np.eye(n)[k])
        bm, cm, *_ = f64_bc(y - s * np.eye(n)[k])
        return np.r_[(bp - bm) / (2 * s), (cp - cm) / (2 * s)]
    cols = []
    for k in range(n):
        c1 = col(h); c2 = col(2 * h)
        cols.append((4 * c1 - c2) / 3)                    # 4th-order Richardson
    return np.array(cols).T                               # 28 x 29

def newton_project(y, iters=60, tol=1e-15):
    for _ in range(iters):
        a = a0 + Nr @ y
        c = shape(a)[1][13:21]
        if not np.all(np.isfinite(c)) or np.abs(c).max() < tol:
            break
        J = np.column_stack([(shape(a0 + Nr @ (y + np.eye(29)[k] * 1e-7))[1][13:21] - c) / 1e-7
                             for k in range(29)])
        y = y - pinv(J) @ c
    return y

def defect(y, lam, J=None):
    """tangential projection of Σ λ_f ∇b_f ; 29-vector (lives in the 21-dim tangent space)."""
    if J is None:
        J = f64_jac(y)
    J8, Wg = J[20:], J[:20]
    P = J8.T @ pinv(J8 @ J8.T) @ J8
    return (np.eye(29) - P) @ (Wg[act].T @ lam)

# ---------------- (0) calibration ---------------------------------------------------------
r0, con0, d0 = shape(a0)
cal = dict(n_active_saved=int(len(act)), lam_min=float(lam_saved.min()), sum_lam_saved=float(lam_saved.sum()),
           stationarity_saved_reported=M['station'], R_model=float(r0),
           res21_model=float(abs(con0).max()), Tcert_float=float(mp.mpf(Tcert_str)),
           C529_float=float(mp.mpf(C529_str)),
           defect_f64_at_a0=float(np.linalg.norm(defect(np.zeros(29), lam18))))
print('[0] calibration:', json.dumps(cal))

# ---------------- (1)(2) high-precision Jacobian + λ uniqueness ---------------------------
def mp_jac_arrays(y):
    G = np.array([[float(x) for x in row] for row in MM.jac_mp(bc, None) if True]) if False else None
    # jac_mp differentiates at y=0 only; for a shifted point we shift the model
    return None

G = np.array([[float(x) for x in row] for row in MM.jac_mp(bc)])
J8, Wg = G[20:], G[:20]
svJ = np.linalg.svd(J8, compute_uv=False)
Pt = np.eye(29) - J8.T @ np.linalg.inv(J8 @ J8.T) @ J8
Ma = Pt @ Wg[act].T
svM = np.linalg.svd(Ma, compute_uv=False)
res_saved_mp = float(np.linalg.norm(Ma @ lam_saved))

def ls_simplex(x0):
    return minimize(lambda l: float(np.linalg.norm(Ma @ l) ** 2), x0, method='SLSQP',
                    constraints=[{'type': 'eq', 'fun': lambda l: l.sum() - 1.0}],
                    bounds=[(0.0, 1.0)] * 18, options={'maxiter': 800, 'ftol': 1e-24})

o1, o2 = ls_simplex(np.ones(18) / 18), ls_simplex(lam_saved.copy())
best = o2.x if np.linalg.norm(Ma @ o2.x) <= np.linalg.norm(Ma @ o1.x) else o1.x
res_star = float(np.linalg.norm(Ma @ best))
U_, S_, Vt_ = np.linalg.svd(Ma)
nz = Vt_[S_ < 1e-9]
lam_uni = (nz[0] / nz[0].sum()) if (len(nz) == 1 and abs(nz[0].sum()) > 1e-12) else None
print('[1] sv(J8) min=%.3f ; sv(M) top-3 min values = %s ; σ_18/σ_17 = %.2e'
      % (svJ.min(), np.array2string(S_[-3:], precision=6), S_[-1] / S_[-2]))
print('    ||M λ_saved|| = %.3e ; ||M λ*|| = %.3e ; null dim(σ<1e-9)=%d'
      % (res_saved_mp, res_star, len(nz)))
if lam_uni is not None:
    print('    unique λ from null vector: max|λ−λ_saved| = %.3e  min=%.4e  sum=%.15f'
          % (float(abs(lam_uni - lam_saved).max()), lam_uni.min(), lam_uni.sum()))

# ---------------- (3) point refinement (λ fixed) ------------------------------------------
print('[2] point refinement: Gauss-Newton on M(y)λ_saved = 0 along the manifold (λ untouched)')
y = np.zeros(29); hist = []
for it in range(30):
    y = newton_project(y)
    d = defect(y, lam18)
    hist.append(dict(it=it, norm=float(np.linalg.norm(d)), dist_y=float(np.linalg.norm(y))))
    if np.linalg.norm(d) < 1e-15:
        break
    J = f64_jac(y); J8y = J[20:]
    Z = null_space(J8y)
    Dd = np.column_stack([(defect(newton_project(y + 1e-7 * Z[:, k]), lam18) - d) / 1e-7 for k in range(21)])
    xi = -np.linalg.lstsq(Dd, d, rcond=None)[0]
    nx = np.linalg.norm(xi)
    if nx > 1e-5:
        xi = xi * (1e-5 / nx)
    y = newton_project(y + Z @ xi)
    if nx < 1e-15:
        break
y_ref = y.copy()
# high-precision defect at a0 and at the refined point (Jacobian rebuilt by shifting the model)
def mp_defect(yv):
    bc2 = MM.make_mp_model(dict(M, a0=a0 + Nr @ yv))
    G2 = np.array([[float(x) for x in row] for row in MM.jac_mp(bc2)])
    J2, W2 = G2[20:], G2[:20]
    P2 = J2.T @ np.linalg.inv(J2 @ J2.T) @ J2
    return float(np.linalg.norm((np.eye(29) - P2) @ (W2[act].T @ lam18))), J2, W2
d_a0_mp = res_saved_mp
d_ref_mp, J8r, Wgr = mp_defect(y_ref)
print('[2] defect ||M(y)λ_saved||: at a0 (50-digit) = %.3e ; after refinement = %.3e ; ||Δy|| = %.3e'
      % (d_a0_mp, d_ref_mp, np.linalg.norm(y_ref)))

# λ uniqueness at the refined point
Ptr = np.eye(29) - J8r.T @ np.linalg.inv(J8r @ J8r.T) @ J8r
Mar = Ptr @ Wgr[act].T
svMr = np.linalg.svd(Mar, compute_uv=False)
nzr = np.linalg.svd(Mar)[2][np.linalg.svd(Mar)[1] < 1e-9]
print('[2] at refined point: σ_18=%.3e σ_17=%.3e ; null dim(σ<1e-9)=%d ; ||M_r λ_saved||=%.3e'
      % (svMr[-1], svMr[-2], len(nzr), float(np.linalg.norm(Mar @ lam18))))
lam_r = (nzr[0] / nzr[0].sum()) if (len(nzr) == 1 and abs(nzr[0].sum()) > 1e-12) else lam_saved

# ---------------- (4) Hessians and the correct reduced Hessian ----------------------------
def hess(f, h=2e-3):
    n = 29; H = np.zeros((n, n)); f0 = f(np.zeros(n))
    for i in range(n):
        ei = np.eye(n)[i]
        d1 = (f(2 * h * ei) - 2 * f0 + f(-2 * h * ei)) / (2 * h) ** 2
        d2 = (f(h * ei) - 2 * f0 + f(-h * ei)) / h ** 2
        H[i, i] = (4 * d2 - d1) / 3
    for i in range(n):
        for j in range(i + 1, n):
            ei, ej = np.eye(n)[i], np.eye(n)[j]
            D1 = (f(2 * h * (ei + ej)) - f(2 * h * (ei - ej)) - f(2 * h * (-ei + ej)) + f(-2 * h * (ei + ej))) / (4 * (2 * h) ** 2)
            D2 = (f(h * (ei + ej)) - f(h * (ei - ej)) - f(h * (-ei + ej)) + f(-h * (ei + ej))) / (4 * h ** 2)
            H[i, j] = H[j, i] = (4 * D2 - D1) / 3
    return H

def bc_shift(yv):
    """float64 (b, c8) function of y measured from the refined point y_ref."""
    def f(y):
        a = a0 + Nr @ (yv + y)
        r, con, d = shape(a)
        return d['logg'] + math.log(max(d['rat'][0], 1e-100)), con[13:21]
    return f

fshift = bc_shift(y_ref)
t1 = time.time()
Hb = [hess(lambda y, f=f: fshift(y)[0][f]) for f in range(20)]
Hc = [hess(lambda y, j=j: fshift(y)[1][j]) for j in range(8)]
print('[3] 28 Hessians (Richardson, h=2e-3) at the refined point in %.1f s' % (time.time() - t1))

mu8 = -np.linalg.solve(J8r @ J8r.T, J8r @ (Wgr[act].T @ lam_saved))
Hphi = sum(lam_saved[i] * Hb[act[i]] for i in range(18))
HL = Hphi + sum(mu8[j] * Hc[j] for j in range(8))
Z = null_space(J8r)
Hred_L = Z.T @ HL @ Z; Hred_L = 0.5 * (Hred_L + Hred_L.T)
Hred_0 = Z.T @ Hphi @ Z; Hred_0 = 0.5 * (Hred_0 + Hred_0.T)
evL, ev0 = np.linalg.eigvalsh(Hred_L), np.linalg.eigvalsh(Hred_0)
print('[4] reduced Hessian (21-dim) at refined point, λ = λ_saved:')
print('    WITH normal correction : min=%.6e max=%.6e n_neg=%-2d' % (evL.min(), evL.max(), int((evL < -1e-8).sum())))
print('    WITHOUT (old, void)    : min=%.6e max=%.6e n_neg=%-2d' % (ev0.min(), ev0.max(), int((ev0 < -1e-8).sum())))
print('    normal-correction shift on min eig: %+.6e   |μ8| = %s'
      % (evL.min() - ev0.min(), np.array2string(np.abs(mu8), precision=4, max_line_width=180)))
w_, V_ = np.linalg.eigh(Hred_L)
v = Z @ V_[:, 0]; v = v / np.linalg.norm(v)          # 29-dim direction (unit in y-space)
pred = float(w_[0])                                   # = vᵀH_red v  (min eigenvalue)

# step-size robustness of the corrected min eigenvalue (same matrices, h -> h/2)
Hb2 = [hess(lambda y, f=f: fshift(y)[0][f], h=1e-3) for f in range(20)]
Hc2 = [hess(lambda y, j=j: fshift(y)[1][j], h=1e-3) for j in range(8)]
HL2 = sum(lam_saved[i] * Hb2[act[i]] for i in range(18)) + sum(mu8[j] * Hc2[j] for j in range(8))
evL2 = np.linalg.eigvalsh(Z.T @ (0.5 * (HL2 + HL2.T)) @ Z)
print('[4b] corrected min eig at h=1e-3: %.6e  (h=2e-3 gave %.6e)' % (evL2.min(), evL.min()))

# ---------------- (5) direction + halving ladder ------------------------------------------
def rec(yv):
    a = a0 + Nr @ (y_ref + yv)
    r, con, d = shape(a)
    al, ww = d['alpha'], d['w']
    mar = min(a[:33].min(), (math.pi - a[:33]).min(), a[33:42].min(), (math.pi / 2 - a[33:42]).min(),
              al.min(), (math.pi - al).min(), ww.min(), (math.pi - ww).min())
    gg = np.exp(d['logg']); u = gg / gg.max()
    return dict(phi=float(lam_saved @ (d['logg'][act] + math.log(d['rat'][0]))), R=float(r),
                res21=float(abs(con).max()), res8=float(abs(con[13:21]).max()), margin=float(mar),
                spread=float(-(lam_saved @ np.log(u[act]))))

phi0 = rec(np.zeros(29))['phi']
lad = []
t = 1e-2
for _ in range(7):
    yv = newton_project(y_ref + t * v) - y_ref
    d = rec(yv); d['t'] = t; d['dphi'] = d['phi'] - phi0; d['ratio'] = d['dphi'] / t ** 2
    d['in_main_domain'] = bool(d['R'] < 0.38)
    lad.append(d); t /= 2
print('[5] halving ladder along the min-eigenvector (reprojected to all 8 equalities):')
for d in lad:
    print('    t=%.3e  ΔΦ=%+.6e  ΔΦ/t²=%+.6e  R=%.15f  max|res21|=%.1e  margin=%.4f  R<0.38=%s'
          % (d['t'], d['dphi'], d['ratio'], d['R'], d['res21'], d['margin'], d['in_main_domain']))
print('    predicted quadratic coefficient ½vᵀH_Lv = %+.6e' % (0.5 * pred))

out = dict(scope='phase-3 corrected: λ-uniqueness + normal-corrected reduced Hessian + one direction; numeric',
           calibration=cal, sv_J8=svJ.tolist(), sv_Ma=svM.tolist(),
           lambda_uniqueness=dict(sv_Ma_top3=S_[-3:].tolist(), res_saved=res_saved_mp, res_star=res_star,
                                  null_dim_1e9=int(len(nz)), lam_star=best.tolist(),
                                  lam_uni=(lam_uni.tolist() if lam_uni is not None else None),
                                  max_abs_lam_uni_minus_saved=(float(abs(lam_uni - lam_saved).max()) if lam_uni is not None else None)),
           point_refinement=dict(dist_y=float(np.linalg.norm(y_ref)), defect_at_a0=d_a0_mp,
                                 defect_after=d_ref_mp, y_ref=y_ref.tolist(), trace=hist,
                                 sv_Ma_refined=svMr.tolist(), null_dim_refined=int(len(nzr))),
           multipliers=dict(mu8=mu8.tolist(), mu_saved_nonlin=mu_saved[13:21].tolist()),
           hessian=dict(eig_corrected=evL.tolist(), eig_uncorrected=ev0.tolist(),
                        min_corrected=float(evL.min()), min_uncorrected=float(ev0.min()),
                        shift=float(evL.min() - ev0.min()), direction_v=v.tolist(),
                        predicted=0.5 * pred, Hred_L=Hred_L.tolist(), Z=Z.tolist(), h=2e-3,
                        min_corrected_h1e3=float(evL2.min()), n_neg_corrected_h1e3=int((evL2 < -1e-8).sum())),
           ladder=lad, phi0=phi0, runtime_s=round(time.time() - T0, 1))
(OUT / 'phase3_lambda_hessian.json').write_text(json.dumps(out, indent=2))
print('[done] %.1f s -> out/phase3_lambda_hessian.json' % (time.time() - T0))
