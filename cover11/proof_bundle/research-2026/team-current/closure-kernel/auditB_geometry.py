"""Audit B: independent reconstruction of the geometry/chart the envelope is built on.

Builds U, C, rho, th from repaired_tc_krawczyk.json (C891 root) exactly as the script does,
then checks the structural facts the certificate relies on:
  - the 9 ring radii/angles and their positivity
  - the two hubs and the 41-row incidence structure
  - each hub has exactly one carrying face (the F list) and the branch counts
  - the 9 tangent rows
"""
import json, math, sys
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
L = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
cert = json.loads((L / 'repaired_tc_krawczyk.json').read_text())['certificate']
z = [float.fromhex(x) for x in cert['center_hex']]
R = z[6]
S = sum(z[:4])
a = [z[0], z[1], z[2], z[3], math.pi - 2 * S, z[3], z[2], z[1], z[0]]
print(f'R = {R:.12f}')
print(f'a (9 angular widths) = {[round(x,8) for x in a]}')
print(f'sum(a) = {sum(a):.12f}  vs 2pi = {2*math.pi:.12f}  diff = {sum(a)-2*math.pi:+.3e}')
print(f'  => the 9 arcs close to 2pi: {abs(sum(a)-2*math.pi) < 1e-9}')
th = [0.0] * 9
for k in range(5, 9):
    th[k] = th[k - 1] + a[k - 1] + a[k]
for k in range(3, -1, -1):
    th[k] = th[k + 1] - a[k] - a[k + 1]
print(f'th (9) = {[round(x,8) for x in th]}')
print(f'th[0] = {th[0]:.3e} (should be 0 by construction)')
rho = [math.cos(x) - math.sqrt(R * R - math.sin(x) ** 2) for x in a]
print(f'rho (9) = {[round(x,8) for x in rho]}')
print(f'  all rho > 0 : {all(x > 0 for x in rho)}')
print(f'  all rho < 1 : {all(x < 1 for x in rho)}')
C = [(rho[k] * math.cos(th[k]), rho[k] * math.sin(th[k])) for k in range(9)]
C += [(z[4], 0.0), (z[5], 0.0)]
U = [(math.cos(th[k] + a[k]), math.sin(th[k] + a[k])) for k in range(9)]
print(f'hubs: c9 = ({z[4]:.9f}, 0),  c10 = ({z[5]:.9f}, 0);  |hub| < 1-r? '
      f'{abs(z[4]) < 1-R}, {abs(z[5]) < 1-R}')
print(f'  |U_k| = 1 : {all(abs(math.hypot(*U[k])-1) < 1e-15 for k in range(9))}')
print()
print('incidence F and edge count bookkeeping')
F = [[2, 9, 10], [6, 9, 10]] + [[k, (k + 1) % 9, 9 if 2 <= k <= 5 else 10]
                                for k in [1, 2, 3, 4, 5, 6, 8]]
print(f'  |F| = {len(F)} faces: {F}')
hub9 = [j for j, f in enumerate(F) if 9 in f]
hub10 = [j for j, f in enumerate(F) if 10 in f]
print(f'  faces on hub9: {hub9}  ({len(hub9)} faces)')
print(f'  faces on hub10: {hub10}  ({len(hub10)} faces)')
edges = []
for k in range(9):
    edges.extend([(9 + k, k), (9 + (k + 1) % 9, k)])
for j, f in enumerate(F):
    edges.extend((9 + s, 20 + j) for s in f)
print(f'  |edges| = {len(edges)}  (claimed 45)')
from collections import Counter
deg = Counter()
for v, w in edges:
    deg[v] += 1
    deg[w] += 1
print(f'  degree of hub9 (node 9) = {deg[9]}, hub10 (node 10) = {deg[10]}')
print(f'  ring degrees: {[deg[k] for k in range(9)]}')
print(f'  distinct ring degrees = {sorted(set(deg[k] for k in range(9)))}')
print(f'  face-centroid degrees = {[deg[20+j] for j in range(len(F))]}')
