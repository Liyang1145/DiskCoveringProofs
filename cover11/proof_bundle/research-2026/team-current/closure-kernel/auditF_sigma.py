"""Audit F: settle the sigma direction with the actual G8 numerical values."""
import json, math, sys
import numpy as np
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
L = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
cert = json.loads((L / 'repaired_tc_krawczyk.json').read_text())['certificate']
z = [float.fromhex(x) for x in cert['center_hex']]
R = z[6]; S = sum(z[:4])
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
    v = (B[0]-A[0], B[1]-A[1]); w = (Cc[0]-A[0], Cc[1]-A[1])
    d = ((B[0]**2+B[1]**2)-(A[0]**2+A[1]**2))/2
    e = ((Cc[0]**2+Cc[1]**2)-(A[0]**2+A[1]**2))/2
    det = v[0]*w[1]-v[1]*w[0]
    return ((d*w[1]-e*v[1])/det, (v[0]*e-w[0]*d)/det)


X = U + C + [cc(f) for f in F]


def dot(p, q):
    return p[0]*q[0]+p[1]*q[1]


edges = []
for k in range(9):
    edges.extend([(9+k, k), (9+(k+1) % 9, k)])
for j, f in enumerate(F):
    edges.extend((9+s, 20+j) for s in f)

# rebuild B with midpoint alpha = 1/45 (rank/geometry only) -- but G8 needs the real alpha.
# Instead reuse the JSON alpha intervals to form the midpoints, as the script does.
d = json.loads((L / 'interval_network_envelope.json').read_text())
al = [ (float(lo)+float(hi))/2 for lo, hi in d['alpha_intervals_diagnostic'] ]
B = np.zeros((41, 45)); T = np.zeros((9, 45))
for j, (v, w) in enumerate(edges):
    dd = (X[v][0]-X[w][0], X[v][1]-X[w][1])
    for node, sgn in [(v, 1), (w, -1)]:
        if node >= 9:
            for k in range(2):
                B[2*(node-9)+k, j] += sgn*dd[k]
        else:
            T[node, j] += 2*sgn*dot(dd, (-U[node][1], U[node][0]))
    B[40, j] = 1

# solve B p = 0 with normalization? use the JSON alpha as the radial stress directly
alpha = np.array(al)
print('alpha from JSON: len', len(alpha), 'sum', alpha.sum(), 'min', alpha.min())
print('B @ alpha (should be ~0 except the norm row):')
r = B @ alpha
print('  sup |B alpha| rows 0:40 =', np.max(np.abs(r[:40])), '  row 40 =', r[40])

# N from the JSON free columns
free = d['stress_free_columns']
dep = [j for j in range(45) if j not in free]
BD = B[:, dep]; BF = -B[:, free]
ND = np.linalg.solve(BD, BF)
N = np.zeros((45, 4))
N[dep] = ND
N[free] = np.eye(4)
print('sup |B N| =', np.max(np.abs(B @ N)))
G = T @ N
print('G (9x4) singular values:', np.round(np.linalg.svd(G, compute_uv=False), 8))
G8 = G[:8]
sv8 = np.linalg.svd(G8, compute_uv=False)
print('G8 (8x4) singular values:', np.round(sv8, 10))
print('  sigma_min(G8) =', sv8[-1])
M = G8.T @ G8
w, V = np.linalg.eigh(M)
print('  eig(G8^T G8) =', np.round(w, 12))
print('  sqrt(min eig)      =', math.sqrt(w[0]))
Ginv = np.linalg.inv(M)
ninf = np.max(np.abs(Ginv).sum(axis=1))
n2 = np.linalg.norm(Ginv, 2)
print('  ||(G8^TG8)^-1||_inf =', ninf)
print('  ||(G8^TG8)^-1||_2   =', n2, '  (equal up to rounding => symmetric, as claimed)')
print('  code sigma = 1/sqrt(||.||_inf) =', 1/math.sqrt(ninf))
print('  => sigma <= sigma_min(G8):', 1/math.sqrt(ninf) <= sv8[-1] + 1e-12)
print('  JSON sigma_lower =', d['quantitative_local_patch']['sigma_lower'][:22])
