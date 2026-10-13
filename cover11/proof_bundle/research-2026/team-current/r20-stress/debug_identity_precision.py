"""Why does the identity check C4 show ~1e-13 absolute error?  Compare midpoint(G) with T*midpoint(N),
and re-check the identity with a consistent pair (G_consistent = T8 @ N_mid)."""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
W = Path(__file__).parent; LEAD = W.parent / 'lead'
ns = {'__file__': str(LEAD / 'interval_network_envelope.py')}
exec((LEAD / 'interval_network_envelope.py').read_text(encoding='utf-8').split("out={'quantitative_local_patch'")[0], ns)
mid = ns['mid']
T8 = np.array([[float(mid(ns['T'][i, j])) for j in range(45)] for i in range(8)])
Nf = np.array([[float(mid(ns['N'][i, j])) for j in range(4)] for i in range(45)])
Gf = np.array([[float(mid(ns['G'][i, j])) for j in range(4)] for i in range(8)])
print('||midpoint(G) - T8 midpoint(N)||_max =', abs(Gf - T8 @ Nf).max())
print('||G||_max =', abs(Gf).max())
tau = 1468.0
Gc = T8 @ Nf                              # consistent pair G' = T8 N'
Q = tau * Nf @ Gf.T                       # 45x8 with midpoint G
Qc = tau * Nf @ Gc.T
# identity: (Q^T T8^T)_{jk} = tau (G' G'^T)_{jk}
M1 = Q.T @ T8.T
M2 = Qc.T @ T8.T
print('max|Q^T T8^T - tau G G^T| (midpoint G) =', abs(M1 - tau * Gf @ Gf.T).max())
print('same with consistent pair                =', abs(M2 - tau * Gc @ Gc.T).max())
print('||midpoint(G) - T8 midpoint(N)||_max =', abs(Gf - Gc).max())
print('tau*||G||_F^2 =', tau * (Gf ** 2).sum())
