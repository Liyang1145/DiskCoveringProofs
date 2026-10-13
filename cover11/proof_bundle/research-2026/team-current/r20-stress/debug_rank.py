"""Rank/bookkeeping checks: rank(B), B N = 0, 1^T N = 0, critical kernel dimension."""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
W = Path(__file__).parent; LEAD = W.parent / 'lead'
ns = {'__file__': str(LEAD / 'interval_network_envelope.py')}
exec((LEAD / 'interval_network_envelope.py').read_text(encoding='utf-8').split("out={'quantitative_local_patch'")[0], ns)
mid = ns['mid']
Bf = np.array([[float(mid(ns['B'][i, j])) for j in range(45)] for i in range(41)])
Nf = np.array([[float(mid(ns['N'][i, j])) for j in range(4)] for i in range(45)])
Gf = np.array([[float(mid(ns['G'][i, j])) for j in range(4)] for i in range(9)])
print('rank(B)=%d  rank(B[:40])=%d  ||BN||=%.2e  1^T N=%.2e' % (
    np.linalg.matrix_rank(Bf, tol=1e-9), np.linalg.matrix_rank(Bf[:40], tol=1e-9),
    abs(Bf @ Nf).max(), abs(Nf.sum(0)).max()))
print('rank(G8^T)=%d  critical kernel dim=%d  ||G8||_F=%.6f' % (
    np.linalg.matrix_rank(Gf[:8].T, tol=1e-9), 8 - np.linalg.matrix_rank(Gf[:8].T, tol=1e-9),
    np.linalg.norm(Gf[:8])))
