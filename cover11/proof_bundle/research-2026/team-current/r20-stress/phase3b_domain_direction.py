"""Phase 3b: (i) λ-uniqueness readout at the refined stationary point; (ii) domain-compatible
negative direction check: restrict to the subspace where the R-active branches are first-order
stationary (max_f ∇b_f·v ≤ 0 forces ∇b_f·v = 0 for all f ∈ A, since Σλ∇b_f ∈ N), so that the
direction does not immediately leave the main domain {R ≤ 0.38}; (iii) explicit ladder.
Also records R at the refined point and the R-rate along the phase-3 direction.

Writes only inside research-2026/team-current/r20-stress/out .
"""
import os, json, math, time
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
from scipy.linalg import null_space, pinv

import mp_model_r20 as MM

W_DIR = Path(__file__).parent; OUT = W_DIR / 'out'
T0 = time.time()
M = MM.load()
ns, shape, Nr, a0 = M['ns'], M['shape'], M['Nr'], M['a0']
lam_saved, act = np.asarray(M['lam']), np.asarray(M['act'])
bc = MM.make_mp_model(M)
P3 = json.loads((OUT / 'phase3_lambda_hessian.json').read_text())
y_ref = np.array(P3['point_refinement']['y_ref'])
Hred_L = np.array(P3['hessian']['Hred_L'])

# ---- Jacobian at the refined point (50-digit) -------------------------------------------
bc_ref = MM.make_mp_model(dict(M, a0=a0 + Nr @ y_ref))
G = np.array([[float(x) for x in row] for row in MM.jac_mp(bc_ref)])
J8, Wg = G[20:], G[:20]
Pt = np.eye(29) - J8.T @ np.linalg.inv(J8 @ J8.T) @ J8
Ma = Pt @ Wg[act].T
U_, S_, Vt_ = np.linalg.svd(Ma)
nz = Vt_[S_ < 1e-9]
lam_r = nz[0] / nz[0].sum() if len(nz) == 1 else None
print('[λ] at refined point: σ18=%.3e σ17=%.3e  null dim=%d' % (S_[-1], S_[-2], len(nz)))
if lam_r is not None:
    print('    normalized null vector: min=%.6e max=%.6e sum=%.15f  ||λ_r−λ_saved||_inf=%.3e'
          % (lam_r.min(), lam_r.max(), lam_r.sum(), float(abs(lam_r - lam_saved).max())))
    print('    (λ_saved min=%.6e ; positivity of λ_r: %s)'
          % (lam_saved.min(), 'OK' if lam_r.min() > 0 else 'NEGATIVE ENTRY'))
# gauge/redundancy checks
sv_eq = np.linalg.svd(np.asarray(ns['eq'])[:, :42], compute_uv=False)
print('    redundancy check: rank(J8)=%d (σmin=%.3f) ; rank(13 linear)=%d (σmin=%.3f) ; Σλ=1 fixes scale'
      % (int((np.linalg.svd(J8, compute_uv=False) > 1e-8).sum()), np.linalg.svd(J8, compute_uv=False).min(),
         int((sv_eq > 1e-8).sum()), sv_eq.min()))

# ---- refined point geometry --------------------------------------------------------------
def rec(yv):
    a = a0 + Nr @ yv
    r, con, d = shape(a)
    al, ww = d['alpha'], d['w']
    mar = min(a[:33].min(), (math.pi - a[:33]).min(), a[33:42].min(), (math.pi / 2 - a[33:42]).min(),
              al.min(), (math.pi - al).min(), ww.min(), (math.pi - ww).min())
    gg = np.exp(d['logg']); u = gg / gg.max()
    return dict(phi=float(lam_saved @ (d['logg'][act] + math.log(d['rat'][0]))), R=float(r),
                res21=float(abs(con).max()), margin=float(mar),
                n_active=int((u > 1 - 1e-9).sum()), min_gap_to_slack=float(u[5] if True else 0))
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
r_ref = rec(y_ref)
print('[pt] refined point: R=%.17g  Φ=%.17g  max|res21|=%.1e  margin=%.4f  n_active=%d'
      % (r_ref['R'], r_ref['phi'], r_ref['res21'], r_ref['margin'], r_ref['n_active']))

# ---- R-rate along the phase-3 direction v ------------------------------------------------
v3 = np.array(P3['hessian']['direction_v']); v3 /= np.linalg.norm(v3)
rates = Wg[act] @ v3                      # d b_f / dt at first order for active branches
r_rate = float(rates.max())
print('[R] phase-3 direction: R-rate = max_f ∇b_f·v = %+.4f  (min %+.4f) -> exits R<0.38 at t≈%.2e'
      % (r_rate, rates.min(), (0.38 - r_ref['R']) / r_rate))

# ---- domain-compatible subspace: ∇b_f·v = 0 for all 18 active branches -------------------
V0 = null_space(np.vstack([J8, Wg[act]]))          # 26 rows, 29 cols -> dim 3
print('[V0] dim{v ∈ ker J8 : (∇b_f)·v = 0 ∀ f∈A} = %d ; R-rate on V0 = %.1e'
      % (V0.shape[1], float(np.abs(Wg[act] @ V0).max())))
Z = np.array(P3['hessian']['Z'])                   # 29 x 21, ker J8 basis used in phase 3
B0 = Z.T @ V0                                      # V0 = Z @ B0  (orthonormal columns preserved)
Q = B0.T @ Hred_L @ B0
Q = 0.5 * (Q + Q.T)
evQ = np.linalg.eigvalsh(Q)
print('[V0] H_red restricted eigenvalues: %s  (min = %+.6e)' % (np.array2string(evQ, precision=6), evQ.min()))
lad0 = []
if evQ.min() < 0:
    u_ = V0 @ np.linalg.eigh(Q)[1][:, 0]
    u_ = u_ / np.linalg.norm(u_)
    t = 1e-3
    for _ in range(8):
        yv = newton_project(y_ref + t * u_) - y_ref
        d = rec(y_ref + yv); d['t'] = t; d['dphi'] = d['phi'] - r_ref['phi']; d['ratio'] = d['dphi'] / t ** 2
        d['in_main_domain'] = bool(d['R'] < 0.38); lad0.append(d); t /= 2
    print('[V0] halving ladder along V0 direction (R-rate 0 at first order):')
    for d in lad0:
        print('     t=%.3e  ΔΦ=%+.6e  ΔΦ/t²=%+.6e  R=%.15f  max|res21|=%.1e  margin=%.4f  R<0.38=%s'
              % (d['t'], d['dphi'], d['ratio'], d['R'], d['res21'], d['margin'], d['in_main_domain']))
    pred0 = float(u_ @ Hred_L @ u_)
    print('[V0] predicted ½vᵀH_Lv = %+.6e' % (0.5 * pred0))
else:
    pred0 = None
    print('[V0] restricted Hessian PSD -> no domain-compatible negative direction to 2nd order')

out = dict(scope='phase-3b: λ-uniqueness at refined point, R-rate, domain-compatible direction; numeric',
           refined_point=dict(R=r_ref['R'], phi=r_ref['phi'], res21=r_ref['res21'], margin=r_ref['margin'],
                              n_active=r_ref['n_active'], dist_from_a0=float(np.linalg.norm(y_ref))),
           lambda_refined=dict(sv_top3=S_[-3:].tolist(), null_dim=int(len(nz)),
                               lam_r=(lam_r.tolist() if lam_r is not None else None),
                               max_abs_minus_saved=(float(abs(lam_r - lam_saved).max()) if lam_r is not None else None),
                               lam_saved=lam_saved.tolist(), act=act.tolist()),
           phase3_direction=dict(v=v3.tolist(), R_rate=r_rate, rates=rates.tolist(),
                                 exit_t=(0.38 - r_ref['R']) / r_rate),
           V0=dict(dim=int(V0.shape[1]), restricted_eigs=evQ.tolist(), min_eig=float(evQ.min()),
                   predicted_half=0.5 * pred0 if pred0 is not None else None,
                   direction=(u_.tolist() if evQ.min() < 0 else None), ladder=lad0),
           runtime_s=round(time.time() - T0, 1))
(OUT / 'phase3b_domain_direction.json').write_text(json.dumps(out, indent=2))
print('[done] %.1f s' % (time.time() - T0))
