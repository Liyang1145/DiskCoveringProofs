"""Debug the mixed-cubic identity: compare the three terms explicitly."""
import os, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np, mpmath as mp
W = Path(__file__).parent; LEAD = W.parent / 'lead'
ns = {'__file__': str(LEAD / 'interval_network_envelope.py')}
exec((LEAD / 'interval_network_envelope.py').read_text(encoding='utf-8').split("out={'quantitative_local_patch'")[0], ns)
mid = ns['mid']
L0 = np.array([[float(mid(ns['Lam'][i, j])) for j in range(9)] for i in range(9)])
PrintL0 = np.round(L0, 6)
Uf = [(float(mid(x)), float(mid(y))) for (x, y) in ns['U']]
rng = np.random.default_rng(3)
x = rng.normal(size=8); x *= 1e-3 / np.linalg.norm(x); q = np.linalg.norm(x)
v = np.array([[x[j] * -Uf[j][1], x[j] * Uf[j][0]] for j in range(8)]).reshape(16)
w = np.array([[math.cos(x[j]) - 1, math.sin(x[j]) - x[j]] for j in range(8)]).reshape(16)
R8 = np.array([[math.cos(x[j]) - 1 + x[j] ** 2 / 2, math.sin(x[j]) - x[j]] for j in range(8)]).reshape(16)
L8 = L0[:8, :8]; K8 = np.kron(L8, np.eye(2))
Cross = np.array([[L0[i, j] * (Uf[i][0] * Uf[j][1] - Uf[i][1] * Uf[j][0]) for j in range(9)] for i in range(9)])
lhs = 2 * v @ K8 @ w; rem = 2 * v @ K8 @ R8; cubic = -x @ Cross[:8, :8] @ (x ** 2)
print('lhs %.6e  cubic %.6e  rem %.6e  identity_err %.3e' % (lhs, cubic, rem, lhs - (cubic + rem)))
term = 0.0
for i in range(8):
    for j in range(8):
        term += 2 * L8[i, j] * (x[i] * (-Uf[i][1]) * (x[j] ** 2 / 2 * Uf[j][0])
                                + x[i] * Uf[i][0] * (x[j] ** 2 / 2 * Uf[j][1]))
sumc = sum(Cross[i, j] * x[i] * x[j] ** 2 for i in range(8) for j in range(8))
print('2<v,Lam0 x^2U/2> %.6e   sum Cross*x*x^2 %.6e   -cubic %.6e' % (term, sumc, -cubic))
print('Lam0 diag', np.round(np.diag(L0), 6))
print('Lam0 row0', PrintL0[0])
