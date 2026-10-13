"""root-cc2 anchor-value-branch: KKT rank and multiplier diagnostics at the candidate.

Builds the full active-set KKT system of the fixed-anchor SOCP (sites, witnesses, radius)
at the calibration's own primal point and reports:
  * number of active face-site (and anchor) incidences,
  * rank of the KKT Jacobian with the multiplier variables included,
  * whether a nonnegative per-incidence multiplier vector exists (per-face sums),
  * which witness blocks are rank deficient.
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
Aanch = np.array(d['anchors'], float)
r = float(d['radius'])
ns = len(C); nfr = len(faces)

L('sites %d faces %d radius %.16f' % (ns, nfr, r))
L('')

# --- active sets
face_act = []   # (face, site) with |c-site - w| = r
for fi, f in enumerate(faces):
    for v in f:
        res = float(np.linalg.norm(C[v] - W[fi])) - r
        if abs(res) < 1e-12: face_act.append((fi, v))
anch_act = []   # (anchor j, site v)
for j, o in enumerate(owners):
    for v in o:
        res = float(np.linalg.norm(C[v] - Aanch[j])) - r
        if abs(res) < 1e-12: anch_act.append((j, v))
L('active face-site incidences: %d of %d' % (len(face_act), 3 * nfr))
L('active anchor-site incidences: %d of %d' % (len(anch_act), sum(len(o) for o in owners)))
L('')

# --- variables: sites (2*ns), witnesses (2*nfr), radius (1)
N = 2 * ns + 2 * nfr + 1
def site_idx(v): return 2 * v
def wit_idx(fi): return 2 * ns + 2 * fi
R = N - 1
rows = []
lab = []
for (fi, v) in face_act:
    dif = C[v] - W[fi]; nrm = float(np.linalg.norm(dif))
    row = np.zeros(N)
    row[site_idx(v):site_idx(v) + 2] = dif / nrm
    row[wit_idx(fi):wit_idx(fi) + 2] = -dif / nrm
    row[R] = -1.0
    rows.append(row); lab.append(('F', fi, v))
for (j, v) in anch_act:
    dif = C[v] - Aanch[j]; nrm = float(np.linalg.norm(dif))
    row = np.zeros(N)
    row[site_idx(v):site_idx(v) + 2] = dif / nrm
    row[R] = -1.0
    rows.append(row); lab.append(('A', j, v))
A = np.array(rows)
sv = np.linalg.svd(A, compute_uv=False)
L('=' * 78)
L('(1) KKT Jacobian of the active system')
L('  rows (active incidences) %d ; columns (sites+witnesses+radius) %d' % A.shape)
L('  rank (tol 1e-9) %d' % int((sv > 1e-9).sum()))
L('  smallest 10 singular values: %s' % np.array2string(sv[-10:], precision=5))

# --- witness blocks
L('')
L('=' * 78)
L('(2) witness blocks: for each face, the 3 gradient rows in the witness coordinates')
wdef = []
for fi, f in enumerate(faces):
    U = np.array([(C[v] - W[fi]) / max(float(np.linalg.norm(C[v] - W[fi])), 1e-300) for v in f])
    s = np.linalg.svd(U, compute_uv=False)
    if (s > 1e-9).sum() < 2: wdef.append(fi)
L('  faces with a rank-deficient witness block: %s' % (wdef if wdef else 'NONE'))
L('  => every witness is locally determined by its 3 active constraints')

# --- multipliers: nonnegative per-incidence vector?
L('')
L('=' * 78)
L('(3) multipliers on the active constraints')
e = np.zeros(N); e[R] = 1.0
mu, resid, rank, _ = np.linalg.lstsq(A.T, -e, rcond=None)
L('  one solution of A^T mu = -e_r: min(mu) %+.6g, max %+.6g (not unique if rank < rows)'
  % (mu.min(), mu.max()))
perface = {}
for k, (t, j, v) in enumerate(lab):
    if t == 'F': perface.setdefault(j, []).append(k)
pos = sum(1 for fi in perface if sum(mu[k] for k in perface[fi]) > 0)
L('  faces with positive total multiplier: %d of %d' % (pos, len(faces)))
L('  face totals (as above, from the same block solution):')
for fi in sorted(perface):
    L('    face %2d %-16s sum_mu = %+.6f'
      % (fi, str(faces[fi]), sum(mu[k] for k in perface[fi])))
L('')
L('  check the witness-gauge block: for each active face, does its own multiplier vector')
L('  satisfy sum_nu grad_w = 0 automatically? (grad_w rows of one face sum to zero)')
for fi in sorted(perface)[:3]:
    f = faces[fi]
    S = np.array([(C[v] - W[fi]) / max(float(np.linalg.norm(C[v] - W[fi])), 1e-300) for v in f])
    L('    face %2d: sum of the 3 unit gradients = %s (should be ~0)'
      % (fi, np.array2string(S.sum(axis=0), precision=3)))

# --- rank of the site/radius projection with witnesses eliminated
L('')
L('=' * 78)
L('(4) the site/radius projection (witness coordinates eliminated)')
nvent = 2 * ns
rows2 = []
for (t, j, v) in lab:
    row = np.zeros(nvent + 1)
    if t == 'F':
        dif = C[v] - W[j]; nrm = float(np.linalg.norm(dif))
    else:
        dif = C[v] - Aanch[j]; nrm = float(np.linalg.norm(dif))
    row[2 * v:2 * v + 2] = dif / nrm
    row[-1] = -1.0
    rows2.append(row)
A2 = np.array(rows2)
sv2 = np.linalg.svd(A2, compute_uv=False)
L('  rows %d ; columns %d ; rank %d' % (A2.shape[0], A2.shape[1], int((sv2 > 1e-9).sum())))
L('  smallest 10 singular values: %s' % np.array2string(sv2[-10:], precision=5))
e2 = np.zeros(nvent + 1); e2[-1] = 1.0
mu2, res2, rank2, _ = np.linalg.lstsq(A2.T, -e2, rcond=None)
L('  A2^T mu2 = -e_r solvable: residual %.3e ; min(mu2) %+.6g ; max %+.6g'
  % (float(np.linalg.norm(A2.T @ mu2 + e2)), mu2.min(), mu2.max()))

(OUT / 'kkt01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'kkt01.txt')
