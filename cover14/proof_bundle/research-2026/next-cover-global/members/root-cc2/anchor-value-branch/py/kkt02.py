"""root-cc2 anchor-value-branch: exact null-space structure of the active-set KKT matrix.

Builds the KKT Jacobian with columns (sites, face witnesses, radius) and rows = active
face-site incidences + active anchor-site incidences, then reports the right null space in
terms of (site, witness, radius) blocks, and identifies which faces contribute.
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
N = 2 * ns + 2 * nfr + 1; R = N - 1

labels = []
rows = []
for fi, f in enumerate(faces):
    res = [float(np.linalg.norm(C[v] - W[fi])) - r for v in f]
    if max(abs(x) for x in res) > 1e-12: continue
    for v in f:
        dif = C[v] - W[fi]; nrm = float(np.linalg.norm(dif))
        row = np.zeros(N)
        row[2 * v:2 * v + 2] = dif / nrm
        row[2 * ns + 2 * fi:2 * ns + 2 * fi + 2] = -dif / nrm
        row[R] = -1.0
        rows.append(row); labels.append(('F', fi, v))
for j, o in enumerate(owners):
    for v in o:
        dif = C[v] - Aanch[j]; nrm = float(np.linalg.norm(dif))
        row = np.zeros(N)
        row[2 * v:2 * v + 2] = dif / nrm
        row[R] = -1.0
        rows.append(row); labels.append(('A', j, v))
A = np.array(rows)
u, sv, vt = np.linalg.svd(A)
tol = 1e-8
nz = [k for k in range(len(sv)) if sv[k] < tol]
L('KKT Jacobian %s rank %d nullity %d' % (A.shape, int((sv > tol).sum()), len(nz)))
L('')
for k in nz:
    z = vt[k]
    L('null direction (sv=%.2e):' % sv[k])
    L('  |site| %.4f |witness| %.4f |radius| %.4f'
      % (np.linalg.norm(z[:2*ns]), np.linalg.norm(z[2*ns:R]), abs(z[R])))
    nzsite = [(v, z[2*v], z[2*v+1]) for v in range(ns) if np.linalg.norm(z[2*v:2*v+2]) > 1e-8]
    if nzsite:
        L('  sites: %s' % [(v, round(float(a), 4), round(float(b), 4)) for v, a, b in nzsite])
    nzw = [(fi, z[2*ns+2*fi], z[2*ns+2*fi+1]) for fi in range(nfr)
           if np.linalg.norm(z[2*ns+2*fi:2*ns+2*fi+2]) > 1e-8]
    if nzw:
        L('  witnesses: %s' % [(fi, round(float(a), 4), round(float(b), 4)) for fi, a, b in nzw])
L('')
L('active faces and their multiplier sums (from a nonneg solution):')
e = np.zeros(N); e[R] = 1.0
mu, res, rank, _ = np.linalg.lstsq(A.T, -e, rcond=None)
sums = {}
for k, (t, j, v) in enumerate(labels):
    if t == 'F': sums[j] = sums.get(j, 0.0) + mu[k]
L('  face: sum_mu')
for fi in sorted(sums):
    L('    %2d %-16s %+.6f %s' % (fi, str(faces[fi]), sums[fi],
                                  'ZERO' if abs(sums[fi]) < 1e-9 else ''))
L('')
L('active anchor incidences: %d' % sum(1 for t, j, v in labels if t == 'A'))
L('active face incidences: %d' % sum(1 for t, j, v in labels if t == 'F'))

(OUT / 'kkt02.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'kkt02.txt')
