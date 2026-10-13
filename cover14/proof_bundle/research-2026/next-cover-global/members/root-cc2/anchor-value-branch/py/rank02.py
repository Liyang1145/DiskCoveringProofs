"""root-cc2 anchor-value-branch: decisive rank computation.

(a) rank of the active-set KKT Jacobian and its right null space,
(b) rank of the same system after dropping the two slack faces entirely,
(c) rank of the submatrix on the two x-symmetric sites (10, 11) with y-motion only,
    and of the x-only motion at those sites.
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
C = np.array(d['centers'], float); W = np.array(d['witnesses'], float)
faces = [list(map(int, f)) for f in d['faces']]
owners = [list(map(int, o)) for o in d['owners']]
Aanch = np.array(d['anchors'], float)
r = float(d['radius']); ns = len(C); nfr = len(faces)

def build(active_faces):
    N = 2 * ns + 2 * nfr + 1; R = N - 1
    rows = []
    for fi in active_faces:
        for v in faces[fi]:
            dif = C[v] - W[fi]; nrm = float(np.linalg.norm(dif))
            row = np.zeros(N)
            row[2 * v:2 * v + 2] = dif / nrm
            row[2 * ns + 2 * fi:2 * ns + 2 * fi + 2] = -dif / nrm
            row[R] = -1.0
            rows.append(row)
    for j, o in enumerate(owners):
        for v in o:
            dif = C[v] - Aanch[j]; nrm = float(np.linalg.norm(dif))
            row = np.zeros(N)
            row[2 * v:2 * v + 2] = dif / nrm
            row[R] = -1.0
            rows.append(row)
    return np.array(rows)

active_f = [fi for fi in range(nfr) if max(abs(float(np.linalg.norm(C[v] - W[fi])) - r) for v in faces[fi]) < 1e-12]
slack_f = [fi for fi in range(nfr) if fi not in active_f]
L('active faces %s ; slack faces %s' % (active_f, slack_f))
L('')

A_all = build(active_f)
A_no = build([fi for fi in active_f if fi in (0, 1, 2, 3, 5, 6, 8, 9, 11)])
for nm, M in (('with slack faces removed', A_no), ('the relaxed model (no face witnesses)', build([]))):
    sv = np.linalg.svd(M, compute_uv=False)
    L('(a) %s: rows %d cols %d rank %d (tol 1e-9) nullity %d'
      % (nm, M.shape[0], M.shape[1], int((sv > 1e-9).sum()), int((sv < 1e-9).sum())))
    L('    smallest 6 sv: %s' % np.array2string(sv[-6:], precision=5))
L('')

L('(b) which active faces have zero multiplier (the proof\'s six)?')
e = np.zeros(A_all.shape[1]); e[-1] = 1
mu, res, rank, _ = np.linalg.lstsq(A_all.T, -e, rcond=None)
idx = {}
for fi in active_f:
    for v in faces[fi]:
        idx.setdefault(fi, []).append(len(idx) + 0)
pos = 0
for fi in active_f:
    tot = 0.0
    for k, (f2, v2) in enumerate([(f, v) for f in active_f for v in faces[f]]):
        if f2 == fi:
            tot += mu[k]
    pass
# simpler: rebuild with labels
labels = []
for fi in active_f:
    for v in faces[fi]:
        labels.append(('F', fi, v))
for j, o in enumerate(owners):
    for v in o:
        labels.append(('A', j, v))
sums = {}
for k, (t, j, v) in enumerate(labels):
    if t == 'F':
        sums[j] = sums.get(j, 0.0) + mu[k]
for fi in active_f:
    L('    face %2d %-16s sum_mu = %+.6f %s' % (fi, str(faces[fi]), sums.get(fi, 0.0),
                                                'ZERO' if abs(sums.get(fi, 0.0)) < 1e-9 else 'positive'))
L('')

L('(c) the x=0 sites: ranks of the motion subspaces')
# sites 10 and 11 sit at x = 0 (candidates).  Check the constraint rows that involve them.
for s in (10, 11):
    rows = []
    for i, (t, j, v) in enumerate(labels):
        if v == s:
            rows.append(i)
    L('  site %2d appears in %d active constraint rows' % (s, len(rows)))
    L('    its coordinates: (%+.12f, %+.12f)' % (C[s, 0], C[s, 1]))
    L('    the constraint gradients w.r.t. this site all have form (c_v - w_f)/r:')
    for i in rows[:4]:
        t, j, v = labels[i]
        src = W[j] if t == 'F' else Aanch[j]
        g = (C[s] - src) / max(float(np.linalg.norm(C[s] - src)), 1e-300)
        L('       row %d (%s %d) grad = (%+.6f, %+.6f)' % (i, t, j, g[0], g[1]))
L('')
L('(d) is the site/radius projection of the active constraints full rank?')
nvent = 2 * ns
rows2 = []
for (t, j, v) in labels:
    src = W[j] if t == 'F' else Aanch[j]
    dif = C[v] - src; nrm = float(np.linalg.norm(dif))
    row = np.zeros(nvent + 1)
    row[2 * v:2 * v + 2] = dif / nrm
    row[-1] = -1.0
    rows2.append(row)
A2 = np.array(rows2)
sv2 = np.linalg.svd(A2, compute_uv=False)
L('  rows %d cols %d rank %d (tol 1e-9)' % (A2.shape[0], A2.shape[1], int((sv2 > 1e-9).sum())))
L('  smallest 6 sv: %s' % np.array2string(sv2[-6:], precision=5))
e2 = np.zeros(nvent + 1); e2[-1] = 1
mu2, res2, rank2, _ = np.linalg.lstsq(A2.T, -e2, rcond=None)
L('  A2^T mu2 = -e_r residual %.3e ; min(mu2) %+.6g' % (float(np.linalg.norm(A2.T @ mu2 + e2)), mu2.min()))

(OUT / 'rank02.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'rank02.txt')
