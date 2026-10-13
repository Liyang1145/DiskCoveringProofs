"""Audit C: the rank story.

The note says: "The 41x45 normalized harmonic matrix has an invertible 41 column minor, hence full
row rank; its 4 free coordinates construct N exactly. Four selected angular rows give exact rank 4
of G".

(a) Is rank(B) = 41 (41 rows)?
(b) Is rank of the 9 tangent rows = 4, so that 41 + 4 = 45 and the combined system is square and
    nonsingular?
(c) Where does the "4-dimensional normalized stress variation space" come from? A force-balance
    argument says: balances (2x11) + normalization (1) = 23 constraints, leaving 45-23 = 22 free.
    So rank(B+normalization) should be 23 out of 41+1 = 42 rows.
(d) Does the code's selected submatrix of 41 rows really have rank 41, and did the greedy add
    exactly 4 tangent rows?

All numeric rank estimates are diagnostics; the certified statements come from the interval
contractions inside the script (which I verify separately).
"""
import json, math, sys
import numpy as np
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
L = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
cert = json.loads((L / 'repaired_tc_krawczyk.json').read_text())['certificate']
z = [float.fromhex(x) for x in cert['center_hex']]
R = z[6]
S = sum(z[:4])
a = [z[0], z[1], z[2], z[3], math.pi - 2 * S, z[3], z[2], z[1], z[0]]
th = [0.0] * 9
for k in range(5, 9):
    th[k] = th[k - 1] + a[k - 1] + a[k]
for k in range(3, -1, -1):
    th[k] = th[k + 1] - a[k] - a[k + 1]
rho = [math.cos(x) - math.sqrt(R * R - math.sin(x) ** 2) for x in a]
C = [(rho[k] * math.cos(th[k]), rho[k] * math.sin(th[k])) for k in range(9)] + [(z[4], 0.0), (z[5], 0.0)]
U = [(math.cos(th[k] + a[k]), math.sin(th[k] + a[k])) for k in range(9)]
F = [[2, 9, 10], [6, 9, 10]] + [[k, (k + 1) % 9, 9 if 2 <= k <= 5 else 10]
                                for k in [1, 2, 3, 4, 5, 6, 8]]


def cc(f):
    A, B, Cc = [C[k] for k in f]
    v = (B[0] - A[0], B[1] - A[1])
    w = (Cc[0] - A[0], Cc[1] - A[1])
    d = ((B[0] ** 2 + B[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
    e = ((Cc[0] ** 2 + Cc[1] ** 2) - (A[0] ** 2 + A[1] ** 2)) / 2
    det = v[0] * w[1] - v[1] * w[0]
    return ((d * w[1] - e * v[1]) / det, (v[0] * e - w[0] * d) / det)


X = U + C + [cc(f) for f in F]
edges = []
for k in range(9):
    edges.extend([(9 + k, k), (9 + (k + 1) % 9, k)])
for j, f in enumerate(F):
    edges.extend((9 + s, 20 + j) for s in f)
print(f'|edges| = {len(edges)}')

B = np.zeros((41, 45)); T = np.zeros((9, 45))
for j, (v, w) in enumerate(edges):
    d = (X[v][0] - X[w][0], X[v][1] - X[w][1])
    for node, sgn in [(v, 1), (w, -1)]:
        if node >= 9:
            for k in range(2):
                B[2 * (node - 9) + k, j] += sgn * d[k]
        else:
            T[node, j] += 2 * sgn * (d[0] * (-U[node][1]) + d[1] * U[node][0])
    B[40, j] = 1

print('\n=== ranks (numeric, diagnostic) ===')
print(f'  rank(B) = {np.linalg.matrix_rank(B, tol=1e-8)} / 41 rows')
print(f'  rank(T) = {np.linalg.matrix_rank(T, tol=1e-8)} / 9 rows')
print(f'  rank([B;T]) = {np.linalg.matrix_rank(np.vstack((B, T)), tol=1e-8)} / 50 rows')
sv = np.linalg.svd(B, compute_uv=False)
print(f'  B singular values: min={sv[-1]:.3e}  2nd small={sv[-2]:.3e}  ratio={sv[-1]/sv[0]:.3e}')
svT = np.linalg.svd(T, compute_uv=False)
print(f'  T singular values: {np.round(svT, 8)}')
print(f'  rank of the 23-row balance system (B rows 0:40 = 20 balance rows + normalization)?')
print(f'    rank(B[:40]) = {np.linalg.matrix_rank(B[:40], tol=1e-8)} / 40')
print(f'    rank(B[:40] with norm row) = {np.linalg.matrix_rank(B, tol=1e-8)} / 41')

print('\n=== the 5-dimensional solution space of B alpha = 0 ===')
ns = np.linalg.svd(B, full_matrices=True)
Vt = ns[2]
print(f'  dim null(B) = {45 - np.linalg.matrix_rank(B, tol=1e-8)}')
print(f'  null(B) vectors (last rows of Vt^T): residual sup norms')
for i in range(1, 6):
    v = Vt[-i]
    print(f'    {i}: ||B v||_inf = {np.max(np.abs(B @ v)):.3e}   ||v|| = {np.linalg.norm(v):.6f}')
