"""Phase 3c addendum: reconcile the 4-vs-3 Hessian spectra of the lead's earlier diagnostic
(nonlinear_stress_probe.py: eigvalsh(Q^T H Q) on the 4-dim common kernel of [Jc; Jg-gbar])
with my 3-dim V0 spectrum, at the SAME point (candidate a0) and with the same H (the
Lagrangian Hessian H_Phi + sum mu_j H_cj) and the same weights lam.

Reports: eigenvalues of H_L on ker K1 (centred, dim 4) and on ker K3 (raw, dim 3),
plus the R-rate of each kernel direction. Numeric only; no optimisation.
"""
import os, json, math, time
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
from scipy.linalg import null_space

import mp_model_r20 as MM

W_DIR = Path(__file__).parent; OUT = W_DIR / 'out'
M = MM.load()
ns, shape, Nr, a0 = M['ns'], M['shape'], M['Nr'], M['a0']
lam, act = np.asarray(M['lam']), np.asarray(M['act'])
bc = MM.make_mp_model(M)
G = np.array([[float(x) for x in row] for row in MM.jac_mp(bc)])
J8, W = G[20:], G[:20]
Jg = W[act]; gbar = lam @ Jg
K1 = np.vstack([J8, Jg - gbar]); K3 = np.vstack([J8, Jg])
Q1 = null_space(K1, rcond=1e-7); Q3 = null_space(K3)
print('dim ker K1 (centred, rcond 1e-7) =', Q1.shape[1], ' ; dim ker K3 (raw) =', Q3.shape[1])
# H_L at a0
def f64_bc(y):
    a = a0 + Nr @ y
    r, con, d = shape(a)
    return d['logg'] + math.log(max(d['rat'][0], 1e-100)), con[13:21]

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

Hb = [hess(lambda y, f=f: f64_bc(y)[0][f]) for f in range(20)]
Hc = [hess(lambda y, j=j: f64_bc(y)[1][j]) for j in range(8)]
mu8 = -np.linalg.solve(J8 @ J8.T, J8 @ gbar)
Hphi = sum(lam[i] * Hb[act[i]] for i in range(18))
HL = Hphi + sum(mu8[j] * Hc[j] for j in range(8))
ev1 = np.linalg.eigvalsh(Q1.T @ HL @ Q1)
ev3 = np.linalg.eigvalsh(Q3.T @ HL @ Q3)
print('eigs on ker K1 (dim 4):', np.array2string(ev1, precision=6))
print('eigs on ker K3 (dim 3):', np.array2string(ev3, precision=6))
print('lead earlier (a0, their H): [.0413 .0499 .0568 .0590]')
# R-rates: for each kernel basis vector, max_f d b_f (R is max of branches, so rate = max over tied branches)
for tag, Q in (('K1', Q1), ('K3', Q3)):
    Rr = np.array([[float(np.max(Jg @ Q[:, k])), float(np.min(Jg @ Q[:, k]))] for k in range(Q.shape[1])])
    print('%s kernel R-rate ranges (max,min) per direction:' % tag, np.array2string(Rr, precision=4))
out = dict(scope='numeric reconciliation of 4-dim common kernel (lead) vs 3-dim V0 spectra at a0',
           dim_ker_K1_centred=int(Q1.shape[1]), dim_ker_K3_raw=int(Q3.shape[1]),
           eig_ker_K1=ev1.tolist(), eig_ker_K3=ev3.tolist(),
           lead_earlier=[0.0413, 0.0499, 0.0568, 0.0590], mu8=mu8.tolist(),
           K1_sv=np.linalg.svd(K1, compute_uv=False).tolist(),
           K3_sv=np.linalg.svd(K3, compute_uv=False).tolist(),
           R_rate_K1=[[float(np.max(Jg @ Q1[:, k])), float(np.min(Jg @ Q1[:, k]))] for k in range(Q1.shape[1])],
           R_rate_K3=[[float(np.max(Jg @ Q3[:, k])), float(np.min(Jg @ Q3[:, k]))] for k in range(Q3.shape[1])])
(OUT / 'phase3c_spectra_reconciliation.json').write_text(json.dumps(out, indent=2))
print('[done] -> out/phase3c_spectra_reconciliation.json')
