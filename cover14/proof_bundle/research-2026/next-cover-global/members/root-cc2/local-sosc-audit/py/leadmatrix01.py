"""root-cc2 local-sosc-audit: solve the LEAD's exact printed 5x5 and test it.

Lead's lead/local-kkt-matrix-control.json gives (midpoint, all 28x5 rows).  This script
 (1) reconstructs the 5x5 from the printed selected rows and solves it for the weights;
 (2) tests the published weights against the printed rows;
 (3) compares the printed rows with my independent finite-difference rows (site-motion
     convention) row by row, to locate my own discrepancy;
 (4) checks the rank of the printed 28x5 matrix (should be 4).
"""
import json
import sys
from pathlib import Path
import mpmath as mp

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead')
HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
sys.path.insert(0, str(LEAD))
from root_integer_certificate import I, Q, S

mp.mp.dps = 60
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

ctrl = json.loads((LEAD / 'local-kkt-matrix-control.json').read_text())
P('keys: %s' % sorted(ctrl.keys()))
for k, v in ctrl.items():
    if k != 'rows_28x5':
        P('   %s = %s' % (k, str(v)[:200]))
rows = ctrl.get('rows_28x5', ctrl.get('rows'))
P('number of printed rows: %d' % len(rows))
P('first row: %s' % rows[0])
P('last row:  %s' % rows[-1])

# the 5x5: selected rows [28 (normalization), 0, 1, 8, 9] per the lead's message
sel = [28, 0, 1, 8, 9]
M = mp.zeros(5, 5)
for i, j in enumerate(sel):
    for k in range(5):
        M[i, k] = mp.mpf(str(rows[j][k]))
P('')
P('=' * 78)
P('(1) the lead\'s 5x5 from rows %s' % sel)
for i in range(5):
    P('    %s' % [mp.nstr(M[i, k], 12) for k in range(5)])
U, Sv, Vt = mp.svd(M)
P('    singular values: %s' % [mp.nstr(x, 10) for x in Sv])
P('    rank: %d ; det = %s' % (sum(1 for x in Sv if x > mp.mpf('1e-30')), mp.nstr(mp.det(M), 12)))
rhs = mp.matrix([0, 0, 0, 0, 1])
sol = mp.lu_solve(M, rhs)
P('    solution w (M w = e5): %s' % [mp.nstr(x, 12) for x in sol])
P('    sum of solution = %s' % mp.nstr(sum(sol), 12))
P('    all positive: %s' % all(x > 0 for x in sol))

cert = json.loads((LEAD / 'local-sosc-certificate.json').read_text())
from fractions import Fraction as FR
wl = []
for lo, hi in cert['weight_intervals']:
    aa = FR(lo); bb = FR(hi)
    wl.append((mp.mpf(aa.numerator)/aa.denominator + mp.mpf(bb.numerator)/bb.denominator)/2)
P('    published weights: %s' % [mp.nstr(x, 12) for x in wl])
P('    max |sol - published| = %s' % mp.nstr(max(abs(sol[i]-wl[i]) for i in range(5)), 6))

P('')
P('=' * 78)
P('(2) published weights against ALL printed rows (stationarity residual)')
res = []
for j, row in enumerate(rows[:28]):
    r = sum(wl[k]*mp.mpf(str(row[k])) for k in range(5))
    res.append((j, r))
nz = [(j, r) for j, r in res if abs(r) > mp.mpf('1e-14')]
P('    rows with |residual| > 1e-14: %s' % [(j, mp.nstr(r, 6)) for j, r in nz])
P('    max |residual| = %s' % mp.nstr(max(abs(r) for _, r in res), 6))
P('    normalization row value: %s' % sum(wl))

P('')
P('=' * 78)
P('(3) rank of the printed 28x5 matrix')
A = mp.zeros(28, 5)
for j in range(28):
    for k in range(5):
        A[j, k] = mp.mpf(str(rows[j][k]))
U2, Sv2, Vt2 = mp.svd(A)
P('    singular values: %s' % [mp.nstr(x, 8) for x in Sv2])
P('    rank (tol 1e-30): %d' % sum(1 for x in Sv2 if x > mp.mpf('1e-30')))
P('    (document says rank 4: the 5 orbit rows are dependent, kernel dim 1)')
nul = [Vt2[i, 4] for i in range(5)]
P('    null direction: %s' % [mp.nstr(x, 8) for x in nul])
P('    published weights projected on the null direction: w.null = %s'
  % mp.nstr(sum(wl[i]*nul[i] for i in range(5)), 8))
P('    published weights projected on the other 4 singular directions: %s'
  % [mp.nstr(sum(wl[i]*Vt2[i, k] for i in range(5)), 8) for k in range(4)])

P('')
P('=' * 78)
P('(4) my independent rows vs the printed ones (site-motion convention)')
P('    printed rows for coordinates: %s' % [(j, rows[j]) for j in (0, 1, 8, 9)])
P('    (compare with evidence/rank01_28x5.txt for my values)')

(OUT / 'leadmatrix01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'leadmatrix01.txt')
