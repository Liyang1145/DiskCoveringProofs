"""root-cc2 anchor-value-branch: finite diagnostic of the active-set degeneracy at the
C1167 candidate for the FIXED-ANCHOR convex reduction (10/4[879]).

Finite diagnostic only: reads the calibration's own primal solution and computes
  * which face-site inequalities are active and their KKT multipliers (least squares),
  * the witness-block ranks (collinear sites -> rank deficient),
  * the rank of the active-constraint Jacobian on (sites, radius).
"""
import json
import numpy as np
from pathlib import Path

P = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead')
HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)
log = []
def L(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

d = json.loads((P / 'fixed-anchor-convex-probe.json').read_text())['runs'][0]
C = np.array(d['centers'], float)
W = np.array(d['witnesses'], float)
faces = [list(map(int, f)) for f in d['faces']]
owners = [list(map(int, o)) for o in d['owners']]
r = float(d['radius'])
L('fixed-anchor probe: sites %d, faces %d, owner-incedences %d, radius %.16f'
  % (len(C), len(faces), sum(len(o) for o in owners), r))
L('')

L('=' * 78)
L('(1) face-site distances versus r')
act = []
for fi, f in enumerate(faces):
    for v in f:
        dist = float(np.linalg.norm(C[v] - W[fi]))
        act.append((fi, v, dist, dist - r))
na = sum(1 for a in act if abs(a[3]) < 1e-12)
L('  incidences %d ; active (|d-r|<1e-12) %d ; max |d-r| %.3e'
  % (len(act), na, max(abs(a[3]) for a in act)))
L('  per-face residuals d-r:')
for fi, f in enumerate(faces):
    res = ['%.1e' % (float(np.linalg.norm(C[v] - W[fi])) - r) for v in f]
    L('    face %2d %-16s %s' % (fi, str(f), res))

L('')
L('=' * 78)
L('(2) witness-block differential ranks')
L('  the three gradients d/dw |c_v - w| span R^2 iff c_v - w_f are not all parallel')
for fi, f in enumerate(faces):
    U = np.array([C[v] - W[fi] for v in f])
    U = U / np.maximum(np.linalg.norm(U, axis=1, keepdims=True), 1e-300)
    sv = np.linalg.svd(U, compute_uv=False)
    L('    face %2d %-16s singular values %s  rank %d'
      % (fi, str(f), np.array2string(sv, precision=3), int((sv > 1e-9).sum())))

L('')
L('=' * 78)
L('(3) active-constraint Jacobian on (sites, radius); rows = active face-site incidences')
nv = len(C)
rows = []
for fi, f in enumerate(faces):
    for v in f:
        dif = C[v] - W[fi]; nrm = float(np.linalg.norm(dif))
        if nrm < 1e-14: continue
        row = np.zeros(2 * nv + 1)
        row[2 * v:2 * v + 2] = dif / nrm
        row[-1] = -1.0
        rows.append(row)
A = np.array(rows)
sv = np.linalg.svd(A, compute_uv=False)
L('  rows %d ; columns %d ; rank (tol 1e-9) %d' % (A.shape[0], A.shape[1], int((sv > 1e-9).sum())))
L('  smallest 8 singular values: %s' % np.array2string(sv[-8:], precision=5))
L('  largest few: %s' % np.array2string(sv[:5], precision=5))

L('')
L('=' * 78)
L('(4) multipliers on the active face-site constraints')
e = np.zeros(A.shape[1]); e[-1] = 1.0
mu, resid, rank, sv2 = np.linalg.lstsq(A.T, -e, rcond=None)
L('  lstsq rank %d ; residual %.3e ; min(mu) %.6g ; max(mu) %.6g'
  % (rank, float(np.linalg.norm(A.T @ mu + e)), mu.min(), mu.max()))
perface = {}
for k, (fi, v, dist, rr) in enumerate(act):
    perface.setdefault(fi, []).append(k)
L('  face  sum of multipliers over its incidences')
for fi in range(len(faces)):
    s = sum(mu[k] for k in perface[fi])
    L('    face %2d %-16s sum_mu = %+.6f' % (fi, str(faces[fi]), s))

L('')
L('=' * 78)
L('(5) anchor-owner active incidences (boundary side)')
for j, o in enumerate(owners):
    dists = [float(np.linalg.norm(C[v] - W[0]) ) for v in o] if False else None
L('  owners (sites per anchor): %s' % owners)
L('  site norms |c_v| (sites on/near the unit circle should exceed r):')
for v in range(nv):
    L('    site %2d c=(%+.9f, %+.9f)  |c| = %.9f' % (v, C[v][0], C[v][1], float(np.linalg.norm(C[v]))))

(OUT / 'active01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'active01.txt')
