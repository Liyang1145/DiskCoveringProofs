"""root-cc2 anchor-value-branch: identify the exact KKT degeneracy structure.

Computes the right null space of the active-set KKT Jacobian and splits each null vector
into (site, witness, radius) components, to determine whether the degeneracy is confined to
the slack witnesses or also involves site/radius directions.
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

L('sites %d faces %d radius %.16f' % (ns, nfr, r))
# which faces are slack (their 3 residuals all nonzero)
slack = []
active_f = []
for fi, f in enumerate(faces):
    res = [float(np.linalg.norm(C[v] - W[fi])) - r for v in f]
    if max(abs(x) for x in res) < 1e-12: active_f.append(fi)
    else: slack.append(fi)
L('active faces: %s' % active_f)
L('slack  faces: %s' % slack)
L('')

N = 2 * ns + 2 * nfr + 1
R = N - 1
rows = []
kind = []
for fi in active_f:
    for v in faces[fi]:
        dif = C[v] - W[fi]; nrm = float(np.linalg.norm(dif))
        row = np.zeros(N)
        row[2 * v:2 * v + 2] = dif / nrm
        row[2 * ns + 2 * fi:2 * ns + 2 * fi + 2] = -dif / nrm
        row[R] = -1.0
        rows.append(row); kind.append(('F', fi, v))
for j, o in enumerate(owners):
    for v in o:
        dif = C[v] - Aanch[j]; nrm = float(np.linalg.norm(dif))
        row = np.zeros(N)
        row[2 * v:2 * v + 2] = dif / nrm
        row[R] = -1.0
        rows.append(row); kind.append(('A', j, v))
A = np.array(rows)
u, sv, vt = np.linalg.svd(A)
tol = 1e-9
nullity = int((sv < tol).sum())
L('=' * 78)
L('KKT Jacobian %s ; rank %d ; nullity %d' % (A.shape, int((sv > tol).sum()), nullity))
L('smallest 8 singular values: %s' % np.array2string(sv[-8:], precision=6))
L('')
L('right null directions (site / witness / radius decomposition):')
for k in range(nullity):
    z = vt[len(sv) - 1 - k]
    sn = float(np.linalg.norm(z[:2 * ns]))
    wn = float(np.linalg.norm(z[2 * ns:R]))
    rn = float(abs(z[R]))
    L('  null %d: |site| %.3e  |witness| %.3e  |radius| %.3e' % (k + 1, sn, wn, rn))
    if sn > 1e-8:
        L('        site components (nonzero):')
        for v in range(ns):
            vec = z[2 * v:2 * v + 2]
            if np.linalg.norm(vec) > 1e-8:
                L('          site %2d  (%+.4f, %+.4f)' % (v, vec[0], vec[1]))
    if wn > 1e-8:
        L('        witness components (nonzero):')
        for fi in range(nfr):
            vec = z[2 * ns + 2 * fi:2 * ns + 2 * fi + 2]
            if np.linalg.norm(vec) > 1e-8:
                L('          witness of face %2d %-16s (%+.4f, %+.4f)'
                  % (fi, str(faces[fi]), vec[0], vec[1]))

L('')
L('=' * 78)
L('multiplier block: is A^T mu = -e_r solvable and with what face sums?')
e = np.zeros(N); e[R] = 1.0
mu, resid, rank, _ = np.linalg.lstsq(A.T, -e, rcond=None)
L('  residual %.3e ; min(mu) %+.3e ; max(mu) %+.6f' % (float(np.linalg.norm(A.T @ mu + e)), mu.min(), mu.max()))
perface = {}
for k, (t, j, v) in enumerate(kind):
    if t == 'F': perface.setdefault(j, []).append(k)
L('  face  sum_mu (from this particular solution)')
for fi in sorted(perface):
    L('    face %2d %-16s %+.6f   %s' % (fi, str(faces[fi]), sum(mu[k] for k in perface[fi]),
                                         'ACTIVE' if fi in active_f else ''))

L('')
L('=' * 78)
L('slack-face witness directions: are they free (no active constraint touches them)?')
free = []
for fi in slack:
    touched = any((t == 'F' and j == fi) for (t, j, v) in kind)
    free.append((fi, not touched))
L('  slack face witness untouched by any active constraint: %s' % free)

(OUT / 'null01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'null01.txt')
