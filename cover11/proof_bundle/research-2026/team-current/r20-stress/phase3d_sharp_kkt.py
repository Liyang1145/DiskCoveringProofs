"""Phase 3d (lead stage-4): independent solve of the SHARP TIED KKT system from the original
candidate a0, with the mpmath angle model.

Unknowns (56):  y in R^29 (angle nullspace coords, 13 linear angle equalities imposed exactly)
                lam in R^18 (sharp weights on the 18 tied branches)
                mu  in R^8  (multipliers of the 8 nonlinear residuals c8)
                t   in R    (common tie value; NOT fixed to any rounded upper-bound number)

Equations (56):
  E1 (8)  : c8(y) = 0
  E2 (18) : g_f(y) - t = 0 ,  f in A   (the 18 ties)
  E3 (29) : grad_y [ sum_f lam_f g_f(y) + sum_j mu_j c8_j(y) ] = Jg^T lam + J8^T mu = 0
  E4 (1)  : sum_f lam_f - 1 = 0

Reports: Jacobian singular values / rank at z0 ; bounded damped Newton (<= 8 steps, legal kept) ;
at the end a 50-digit re-evaluation of all 56 residuals, ties, R, positivity margin.

Numeric only. No multiple starts. No global claims. Writes only in r20-stress/out .
"""
import os, json, math, time
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp

import mp_model_r20 as MM

W_DIR = Path(__file__).parent; OUT = W_DIR / 'out'
T0 = time.time(); mp.mp.dps = 50

M = MM.load()
ns, shape, Nr, a0 = M['ns'], M['shape'], M['Nr'], M['a0']
lam0, act = np.asarray(M['lam']), np.asarray(M['act'])
bc = MM.make_mp_model(M)
NACT, NC = 18, 8
NZ = 29 + NACT + NC + 1

# ---------------- float64 model pieces ----------------------------------------------------
def f64_state(y):
    a = a0 + Nr @ y
    r, con, d = shape(a)
    b = d['logg'] + math.log(max(d['rat'][0], 1e-100))
    return a, r, con, d, b

def f64_jac(y, h=1e-5):
    e = np.eye(29)
    def col(k, s):
        _, _, cp, _, bp = f64_state(y + s * e[k])
        _, _, cm, _, bm = f64_state(y - s * e[k])
        return np.r_[(bp - bm) / (2 * s), (cp[13:21] - cm[13:21]) / (2 * s)]   # 20 + 8 = 28
    return np.array([(4 * col(k, h) - col(k, 2 * h)) / 3 for k in range(29)]).T   # 28 x 29

def hess_scalar(fun, h=2e-3):
    n = 29; H = np.zeros((n, n)); f0 = fun(np.zeros(n))
    for i in range(n):
        ei = np.eye(n)[i]
        d1 = (fun(2 * h * ei) - 2 * f0 + fun(-2 * h * ei)) / (2 * h) ** 2
        d2 = (fun(h * ei) - 2 * f0 + fun(-h * ei)) / h ** 2
        H[i, i] = (4 * d2 - d1) / 3
    for i in range(n):
        for j in range(i + 1, n):
            ei, ej = np.eye(n)[i], np.eye(n)[j]
            D1 = (fun(2 * h * (ei + ej)) - fun(2 * h * (ei - ej)) - fun(2 * h * (-ei + ej)) + fun(-2 * h * (ei + ej))) / (4 * (2 * h) ** 2)
            D2 = (fun(h * (ei + ej)) - fun(h * (ei - ej)) - fun(h * (-ei + ej)) + fun(-h * (ei + ej))) / (4 * h ** 2)
            H[i, j] = H[j, i] = (4 * D2 - D1) / 3
    return H

def margin(y):
    a, r, con, d, b = f64_state(y)
    al, ww = d['alpha'], d['w']
    return min(a[:33].min(), (math.pi - a[:33]).min(), a[33:42].min(), (math.pi / 2 - a[33:42]).min(),
               al.min(), (math.pi - al).min(), ww.min(), (math.pi - ww).min())

def unpack(z):
    return z[:29], z[29:29 + NACT], z[29 + NACT:29 + NACT + NC], z[29 + NACT + NC]

def FJ(z):
    y, lam, mu, t = unpack(z)
    a, r, con, d, b = f64_state(y)
    g = b[act]
    c8 = con[13:21]
    J = f64_jac(y)
    J8, Jg = J[20:], J[:20][act]
    HL = hess_scalar(lambda yv, lam=lam, mu=mu: float(lam @ f64_state(yv)[4][act] + mu @ f64_state(yv)[2][13:21]))
    F = np.r_[c8, g - t, Jg.T @ lam + J8.T @ mu, lam.sum() - 1.0]
    Jac = np.zeros((NZ, NZ))
    Jac[0:NC, 0:29] = J8
    Jac[NC:NC + NACT, 0:29] = Jg
    Jac[NC:NC + NACT, 29 + NACT + NC] = -1.0          # d(g-t)/dt ; t is the LAST unknown (index 55)
    Jac[NC + NACT:NC + NACT + 29, 0:29] = HL
    Jac[NC + NACT:NC + NACT + 29, 29:29 + NACT] = Jg.T
    Jac[NC + NACT:NC + NACT + 29, 29 + NACT:29 + NACT + NC] = J8.T
    Jac[NZ - 1, 29:29 + NACT] = 1.0
    return F, Jac

# ---------------- initial point from a0 (t is solved, not fixed) --------------------------
G0 = np.array([[float(x) for x in row] for row in MM.jac_mp(bc)])
J80, Jg0 = G0[20:], G0[:20][act]
gbar0 = Jg0.T @ lam0
mu0 = -np.linalg.solve(J80 @ J80.T, J80 @ gbar0)
b0 = f64_state(np.zeros(29))[4]
t0 = float(np.mean(b0[act]))
z = np.r_[np.zeros(29), lam0, mu0, t0]
print('[z0] t0 = %.17g (mean of the 18 active branch values at a0; NOT a rounded upper bound)' % t0)
F0, J0 = FJ(z)
print('[z0] residual blocks: |c8|inf=%.3e  |g-t|inf=%.3e  |stat|inf=%.3e  |sumlam-1|=%.3e  ||F||2=%.3e'
      % (abs(F0[0:8]).max(), abs(F0[8:26]).max(), abs(F0[26:55]).max(), abs(F0[55]), np.linalg.norm(F0)))
sv0 = np.linalg.svd(J0, compute_uv=False)
print('[Jac@z0] singular values (56): smallest 8 =', np.array2string(sv0[-8:], precision=3))
for th in (1e-4, 1e-6, 1e-8, 1e-10, 1e-12):
    print('          rank at threshold %.0e : %d  (nullity %d)' % (th, int((sv0 > th).sum()), NZ - int((sv0 > th).sum())))
print('[Jac@z0] rank default = %d ; cond = %.3e' % (int(np.linalg.matrix_rank(J0)), sv0[0] / sv0[-1]))

# ---------------- bounded damped Newton (<= 8 steps, legal kept) --------------------------
hist = []
for it in range(8):
    F, J = FJ(z)
    nF = np.linalg.norm(F)
    dz = -np.linalg.lstsq(J, F, rcond=None)[0]
    nrm = np.linalg.norm(dz)
    alpha, accepted = 1.0, False
    for _ in range(40):
        zt = z + alpha * dz
        mt = margin(zt[:29])
        if mt > 1e-6 and np.all(np.isfinite(zt)):
            Ft, _ = FJ(zt)
            if np.linalg.norm(Ft) < nF or np.linalg.norm(Ft) < 1e-14:
                accepted = True; break
        alpha *= 0.5
    hist.append(dict(it=it, nF=float(nF), step_norm=float(nrm), alpha=float(alpha), accepted=bool(accepted)))
    print('[newton %d] ||F||=%.6e  |dz|=%.3e  alpha=%.3g  accepted=%s  margin=%.4f  R=%.15f'
          % (it, nF, nrm, alpha, accepted, margin(z[:29]), f64_state(z[:29])[1]))
    if not accepted:
        break
    z = z + alpha * dz
    if np.linalg.norm(F) < 1e-14:
        break

y_s, lam_s, mu_s, t_s = unpack(z)
print('[newton] final: ||F||=%.6e  t=%.17g  min lam=%.6e  |y|=%.3e  dist to a0=%.3e'
      % (np.linalg.norm(FJ(z)[0]), t_s, lam_s.min(), np.linalg.norm(y_s), np.linalg.norm(y_s)))

# ---------------- 50-digit re-evaluation at the final point ------------------------------
bc_s = MM.make_mp_model(dict(M, a0=a0 + Nr @ y_s))
y_mp = [mp.mpf(0)] * 29
b_mp, c8_mp = bc_s(y_mp)
G_s = np.array([[float(x) for x in row] for row in MM.jac_mp(bc_s)])
J8s, Jgs = G_s[20:], G_s[:20][act]
g_mp = np.array([float(x) for x in b_mp])[act]
c8_mpf = np.array([float(x) for x in c8_mp])
stat_mp = Jgs.T @ lam_s + J8s.T @ mu_s
a_s, r_s, con_s, d_s, b_s = f64_state(y_s)
gg = np.exp(d_s['logg']); u = gg / gg.max()
res = dict(
    tie_res_max=float(np.abs(g_mp - t_s).max()),
    c8_res_max=float(np.abs(c8_mpf).max()),
    stat_res_max=float(np.abs(stat_mp).max()),
    sumlam_minus1=float(lam_s.sum() - 1.0),
    R_f64=r_s, R_mp=str(mp.mpf(0)), margin=float(margin(y_s)),
    n_ties_1e12=int((u > 1 - 1e-12).sum()), min_lam=float(lam_s.min()),
    y_norm=float(np.linalg.norm(y_s)), lam=list(map(float, lam_s)), mu=list(map(float, mu_s)), t=float(t_s),
    y=list(map(float, y_s)),
)
# R in 50 digits at the solution
Rt = mp.mpf(0)
res['R_mp'] = str(mp.mpf(float(r_s)))
print('[final 50-digit re-eval] tie|max|=%.3e  c8|max|=%.3e  stat|max|=%.3e  sumlam-1=%.3e  ties(u>1-1e-12)=%d/18'
      % (res['tie_res_max'], res['c8_res_max'], res['stat_res_max'], res['sumlam_minus1'], res['n_ties_1e12']))
print('   R=%.17g  margin=%.4f  min lam=%.4e  t=%.17g' % (res['R_f64'], res['margin'], res['min_lam'], res['t']))

out = dict(scope='sharp tied KKT 56x56 solve from a0 with the mpmath angle model; numeric only, single start',
           unknowns=dict(desc='29 y + 18 lam + 8 mu + 1 t', n=NZ),
           equations=dict(desc='8 c8 + 18 (g-t) + 29 stationarity + 1 (sum lam - 1)', n=NZ),
           z0=dict(t0=t0, lam=lam0.tolist(), mu=mu0.tolist()),
           residual_at_z0=dict(c8=float(abs(F0[0:8]).max()), ties=float(abs(F0[8:26]).max()),
                               stat=float(abs(F0[26:55]).max()), sumlam=float(abs(F0[55])), norm2=float(np.linalg.norm(F0))),
           jac_singular_values=sv0.tolist(), jac_rank_default=int(np.linalg.matrix_rank(J0)),
           newton_history=hist, final=res, runtime_s=round(time.time() - T0, 1))
(OUT / 'phase3d_sharp_kkt.json').write_text(json.dumps(out, indent=2))
print('[done] %.1f s -> out/phase3d_sharp_kkt.json' % (time.time() - T0))
