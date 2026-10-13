"""root-cc2 anchor-value-branch: validation of the six corrections (numeric diagnostic).

Confirms, in the corrected language:
  * the assembled matrix is the PRIMAL active-constraint Jacobian (no multiplier columns);
  * the null space of that Jacobian has a NONZERO site part (so a full-column-rank
    sub-block does not pin the sites when witness motion is allowed);
  * which faces carry zero multiplier at the candidate;
  * the rank of the constraint Jacobian after DROPPING the zero-multiplier faces
    (the relaxed problem whose value is a lower bound for V).
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

def build(face_list, with_witness_cols=True):
    rows = []; labels = []
    for fi in face_list:
        for v in faces[fi]:
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
    return np.array(rows), labels

active = [fi for fi in range(nfr)
          if max(abs(float(np.linalg.norm(C[v] - W[fi])) - r) for v in faces[fi]) < 1e-12]
A, labels = build(active)
L('(0) the assembled matrix is the PRIMAL active-constraint Jacobian: %d rows x %d cols'
  % A.shape)
L('    columns = sites(%d) + witnesses(%d) + radius(1) ; NO multiplier/stationarity rows.'
  % (2 * ns, 2 * nfr))

L('')
L('(1) multipliers per face (least-norm solution of A^T mu = -e_r) and zero-multiplier faces')
e = np.zeros(N); e[R] = 1.0
mu, res, rank, _ = np.linalg.lstsq(A.T, -e, rcond=None)
sums = {}
for k, (t, j, v) in enumerate(labels):
    if t == 'F': sums[j] = sums.get(j, 0.0) + mu[k]
zero_f = [fi for fi in sorted(sums) if abs(sums[fi]) < 1e-9]
pos_f = [fi for fi in sorted(sums) if sums[fi] > 1e-9]
L('    zero-multiplier faces: %s' % zero_f)
L('    positive-multiplier faces: %s' % pos_f)
L('    (least-norm solution min(mu)=%.2e; this is a numeric diagnostic only)' % mu.min())

L('')
L('(2) null space of the primal active Jacobian')
u, sv, vt = np.linalg.svd(A)
tol = 1e-8
nz = [k for k in range(len(sv)) if sv[k] < tol]
L('    rank %d of %d columns; nullity %d (tol %.0e)'
  % (int((sv > tol).sum()), A.shape[1], len(nz), tol))
for k in nz:
    z = vt[k]
    sn = float(np.linalg.norm(z[:2 * ns]))
    wn = float(np.linalg.norm(z[2 * ns:R]))
    rn = abs(float(z[R]))
    L('    null dir (sv=%.1e): |site| %.4f |witness| %.4f |radius| %.4f'
      % (sv[k], sn, wn, rn))
    if sn > 1e-8:
        L('      NONZERO SITE PART -> the site block being full-column-rank does NOT pin')
        L('      the sites once witness motion is allowed.')
        sites = [(v, tuple(np.round(z[2 * v:2 * v + 2], 4))) for v in range(ns)
                 if np.linalg.norm(z[2 * v:2 * v + 2]) > 1e-8]
        L('      sites moved: %s' % sites)

L('')
L('(3) rank after dropping the zero-multiplier faces (the relaxed problem)')
keep = [fi for fi in active if fi not in zero_f]
Arel, labrel = build(keep)
sv2 = np.linalg.svd(Arel, compute_uv=False)
L('    kept faces %s' % keep)
L('    relaxed Jacobian %d rows x %d cols ; rank %d ; nullity %d (tol %.0e)'
  % (Arel.shape[0], Arel.shape[1], int((sv2 > tol).sum()), int((sv2 < tol).sum()), tol))
L('    smallest 8 singular values: %s' % np.array2string(sv2[-8:], precision=5))
# also drop the two slack faces (they are already excluded by `active`)
L('    (faces 14, 15 are slack at the candidate and are already absent from `active`)')

L('')
L('(4) the coordinate convention actually used')
L('    the classifier variables x_j are normalised angular DEFICITS (x = d/D with')
L('    D = 10L-2pi, L = 2 asin U), not site coordinates.  In the site list below the')
L('    x-AXIS sites 8, 9 have y = 0 and x != 0; sites with x-coordinate 0 are 12, 13.')
for v in range(ns):
    L('      site %2d  c = (%+.12f, %+.12f)' % (v, C[v, 0], C[v, 1]))

(OUT / 'validation01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'validation01.txt')
