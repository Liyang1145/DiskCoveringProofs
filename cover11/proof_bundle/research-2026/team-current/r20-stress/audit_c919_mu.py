"""Audit: which matrix/constant reproduces the registered C919 constant mu0=.0022 ?
Also report the C919 coefficient under the numerically computed min eigenvalue, to see whether
the registered conclusion (coefficient > 1e-5 on q<=191/25000) is robust to the discrepancy.
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np, mpmath as mp
W = Path(__file__).parent; LEAD = W.parent / 'lead'; OUT = W / 'out'
ns = {'__file__': str(LEAD / 'interval_network_envelope.py')}
exec((LEAD / 'interval_network_envelope.py').read_text(encoding='utf-8').split("out={'quantitative_local_patch'")[0], ns)
mid = ns['mid']
H9 = np.array([[float(mid(ns['H'][i, j])) for j in range(9)] for i in range(9)])
G9 = np.array([[float(mid(ns['G'][i, j])) for j in range(4)] for i in range(9)])
H8, G8 = H9[:8, :8], G9[:8]
cert = json.loads((LEAD / 'relative_stress_ball_certificate.json').read_text())
Rb = np.array([[float.fromhex(h) for h in row] for row in cert['constants']['basis_R_floathex']])

def eigmin(M):
    return float(np.linalg.eigvalsh((M + M.T) / 2).min())

variants = {
    'H8 + 0.1 G8G8^T (C919 as documented)': H8 + 0.1 * G8 @ G8.T,
    'H9 + 0.1 G9G9^T (9 rows)': H9 + 0.1 * G9 @ G9.T,
    'H8 + 0.1 G8G8^T, projected on ker(G8^T)': None,
    'H8 (no stress term)': H8,
    'H8 + 0.2 G8G8^T': H8 + 0.2 * G8 @ G8.T,
    'H8 + 0.1 G8G8^T + 0.1*I': H8 + 0.1 * G8 @ G8.T + 0.1 * np.eye(8),
    'H9 + 0.1 G9G9^T on 1^perp': None,
}
res = {}
for k, M in variants.items():
    if M is None:
        continue
    res[k] = eigmin(M)
# projected variants
Qk = np.linalg.svd(G8.T)[2][4:].T          # basis of ker(G8^T) in R^8
res['H8 + 0.1G8G8^T on ker(G8^T)'] = eigmin(Qk.T @ (H8 + 0.1 * G8 @ G8.T) @ Qk)
Q1 = np.linalg.svd(np.ones((1, 9)))[2][1:].T
res['H9 + 0.1G9G9^T on 1^perp'] = eigmin(Q1.T @ (H9 + 0.1 * G9 @ G9.T) @ Q1)
res['H9 + 0.1G9G9^T full'] = eigmin(H9 + 0.1 * G9 @ G9.T)
res['C920 dyadic H8+1468 G(R)G(R)^T'] = eigmin(H8 + 1468.0 * (G8 @ Rb) @ (G8 @ Rb).T)
for k, v in res.items():
    print('%-42s %.8f   pass00022=%s pass00020959=%s' % (k, v, v >= 0.0022, v >= 0.0020959))

# C919 coefficient robustness
Cc, dd, tau, tau0 = 0.0358, 0.08, 0.1, 0.05
Bc, Gn, ball = 182.0, 1.892, 191 / 25000
quartic = dd / 3 + tau ** 2 * (Bc * dd + 1.074) ** 2 / (4 * (tau - tau0))
for mu0 in [0.0022, 0.00209588, 0.0020]:
    coef = mu0 / 2 - Cc * ball - quartic * ball ** 2
    print('C919 mu0=%.8f -> coefficient=%.6e  (>1e-5 : %s)' % (mu0, coef, coef > 1e-5))
print('C919 quartic =', quartic, 'positivity product =', tau * Bc * Gn * ball)
(OUT / 'c919_mu_audit.json').write_text(json.dumps(dict(variants=res, quartic=quartic,
    coefficients={str(m): (m / 2 - Cc * ball - quartic * ball ** 2) for m in [0.0022, 0.00209588, 0.0020]}), indent=2))
