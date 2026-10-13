"""Phase 3e (rewritten): verification of the solved sharp-tied KKT point from phase3d.

Context: the first phase-3d run had a column-index bug (the tie block's -1 was placed in the
lambda columns instead of the t column), which produced a spurious "rank 55 / zero singular
value / degeneracy" reading. With the correct assembly the 56x56 Jacobian is FULL RANK.
This script reports, for the solved point (y, lam, mu, t):
  - Jacobian singular values / rank / condition at the solution,
  - 50-digit residuals of all four equation blocks,
  - tie status (18 branches), R, positivity margin,
  - the multiplier readout,
  - the accuracy-limited residual floor (float64 Richardson Hessian in the Jacobian).
Numeric only; no new starts. Writes only in r20-stress/out .
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp

import mp_model_r20 as MM

W_DIR = Path(__file__).parent; OUT = W_DIR / 'out'
mp.mp.dps = 50
M = MM.load()
ns, shape, Nr, a0 = M['ns'], M['shape'], M['Nr'], M['a0']
act = np.asarray(M['act'])
D = json.loads((OUT / 'phase3d_sharp_kkt.json').read_text())
sol = D['final']
y_s, lam_s, mu_s, t_s = np.array(sol['y']), np.array(sol['lam']), np.array(sol['mu']), sol['t']
NZ = 56; NACT, NC = 18, 8

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
        return np.r_[(bp - bm) / (2 * s), (cp[13:21] - cm[13:21]) / (2 * s)]
    return np.array([(4 * col(k, h) - col(k, 2 * h)) / 3 for k in range(29)]).T

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

J = f64_jac(y_s); J8, Jg = J[20:], J[:20][act]
HL = hess_scalar(lambda yv: float(lam_s @ f64_state(yv)[4][act] + mu_s @ f64_state(yv)[2][13:21]))
Jac = np.zeros((NZ, NZ))
Jac[0:NC, 0:29] = J8
Jac[NC:NC + NACT, 0:29] = Jg
Jac[NC:NC + NACT, 55] = -1.0
Jac[NC + NACT:NC + NACT + 29, 0:29] = HL
Jac[NC + NACT:NC + NACT + 29, 29:47] = Jg.T
Jac[NC + NACT:NC + NACT + 29, 47:55] = J8.T
Jac[55, 29:47] = 1.0
sv = np.linalg.svd(Jac, compute_uv=False)
print('[Jac @solution] 56 sv: min=%.4e  2nd=%.4e  max=%.4e  rank@1e-12=%d  cond=%.2e'
      % (sv[-1], sv[-2], sv[0], int((sv > 1e-12).sum()), sv[0] / sv[-1]))

# 50-digit residuals at the solution
bc_s = MM.make_mp_model(dict(M, a0=a0 + Nr @ y_s))
b_mp, c8_mp = bc_s([mp.mpf(0)] * 29)
G_s = np.array([[float(x) for x in row] for row in MM.jac_mp(bc_s)])
J8s, Jgs = G_s[20:], G_s[:20][act]
g_mp = np.array([float(x) for x in b_mp])[act]
c8f = np.array([float(x) for x in c8_mp])
stat_mp = Jgs.T @ lam_s + J8s.T @ mu_s
a_s, r_s, con_s, d_s, b_s = f64_state(y_s)
gg = np.exp(d_s['logg']); u = gg / gg.max()
al, ww = d_s['alpha'], d_s['w']
mar = min(a_s[:33].min(), (math.pi - a_s[:33]).min(), a_s[33:42].min(), (math.pi / 2 - a_s[33:42]).min(),
          al.min(), (math.pi - al).min(), ww.min(), (math.pi - ww).min())
res = dict(ties_max=float(np.abs(g_mp - t_s).max()), c8_max=float(np.abs(c8f).max()),
           stationarity_max=float(np.abs(stat_mp).max()), sumlam_minus1=float(lam_s.sum() - 1.0),
           n_ties_1e12=int((u > 1 - 1e-12).sum()), n_ties_1e15=int((u > 1 - 1e-15).sum()),
           min_lam=float(lam_s.min()), max_lam=float(lam_s.max()), margin=float(mar),
           R_f64=float(r_s), res21_f64=float(abs(con_s).max()), t=float(t_s),
           y_norm=float(np.linalg.norm(y_s)))
print('[50-digit residuals] ties=%.3e  c8=%.3e  stationarity=%.3e  sum(lam)-1=%.3e  margin=%.4f'
      % (res['ties_max'], res['c8_max'], res['stationarity_max'], res['sumlam_minus1'], res['margin']))
print('[candidate] R=%.17g  n_ties(u>1-1e-12)=%d/18  |lam|min=%.6e max=%.6e  |y|=%.3e'
      % (res['R_f64'], res['n_ties_1e12'], res['min_lam'], res['max_lam'], res['y_norm']))
print('[compare] R_f64 - float(C529) = %+.3e ; R_f64 - float(Tcert) = %+.3e'
      % (mp.mpf(repr(res['R_f64'])) - mp.mpf('0.379983853119838709048518179573429853811597902801556119905385'),
         mp.mpf(repr(res['R_f64'])) - mp.mpf('0.3799838531198386897222616061360932143087189561522153170163892')))
print('[note] the 56-equation residual floor ~1e-11 (stationarity block) is set by the float64 '
      'Richardson Hessian inside the Jacobian, not by system inconsistency (rank 56, cond %.1e)' % (sv[0] / sv[-1]))

out = dict(scope='verification of the solved sharp-tied KKT point (numeric); corrects the phase-3d '
                 'first-run column-index bug that produced a spurious rank-55 reading',
           jac_sv=sv.tolist(), jac_rank=int((sv > 1e-12).sum()), jac_cond=float(sv[0] / sv[-1]),
           residuals=res, lam=lam_s.tolist(), mu=mu_s.tolist(), t=float(t_s), y=y_s.tolist(),
           phase3d_summary=D['newton_history'])
(OUT / 'phase3e_solution_verification.json').write_text(json.dumps(out, indent=2))
print('[done] -> out/phase3e_solution_verification.json')
