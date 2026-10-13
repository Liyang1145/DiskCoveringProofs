"""Hand-built exact 3-ring sample near the origin, plus the saved candidate:
resolve the identity between (a) the angle sum of the two fan triangles and
(b) the interior angle of the switch polygon at the switch, and determine the
correct form of the closure equation.

Sample: c_0, c_1 at angles 80,100 deg, radius rho with |P|=1 for P = (0.5,0.866) etc.
We use c_0 = 0.9*(cos80,sin80), c_1 = 0.9*(cos100,sin100)  => the disk boundary
switch on |x|=1 at angle 90 deg has distance rho0 = |P-c_0| = |P-c_1|... we
compute exactly and use that as r.
"""
import numpy as np, math, json
from pathlib import Path
ROOT = Path('.').resolve().parents[2]

def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)

# ---- hand-built sample with three rings at 80,100,260 degrees and radius 0.9
angles = [80, 100, 260]
c = np.array([[0.9*math.cos(math.radians(t)), 0.9*math.sin(math.radians(t))] for t in angles])
# switches between consecutive pairs: 9-ring ordering (we fake the closing ones)
def sw(ca, cb):
    m = 0.5*(ca+cb); d = cb-ca; n = np.array([d[1], -d[0]])/np.linalg.norm(d)
    t0 = -(m @ n); s2 = 1 - m @ m
    return [m + (t0+s*n)*n for s in (1, -1)]

print('c_0,c_1 =', np.round(c[0], 6), np.round(c[1], 6))
cans = sw(c[0], c[1])
print('bisector crossings with |x|=1:', [np.round(x, 6).tolist() for x in cans])
for x in cans:
    print('   at', np.round(x, 6), '|x-c0|=%.6f |x-c1|=%.6f' % (np.linalg.norm(x-c[0]), np.linalg.norm(x-c[1])))
P = cans[0]        # the one on the far side (90 deg)
O = np.array([0.0, 0.0])
print()
print('Take P =', np.round(P, 6), ' r =', np.linalg.norm(P-c[0]))
u = c[0]-P    # not the polygon edge, just diagnostics
# angles at P:
ap_c0 = math.atan2(cross(c[0]-P, c[1]-P), dot(c[0]-P, c[1]-P))
print('angle at P between c0,c1 (signed) =', ap_c0, ' abs =', abs(ap_c0))
# distances
print('|P-c0| =', np.linalg.norm(P-c[0]), ' |P-c1| =', np.linalg.norm(P-c[1]))
print('|c0| =', np.linalg.norm(c[0]), 'sqrt(1-r^2) =', math.sqrt(1-np.linalg.norm(P-c[0])**2))
print('n.(c0-P) =', dot(c[1]-c[0], c[0]-P), ' n.(c1-P) =', dot(c[1]-c[0], c[1]-P))
print()
print('SAVED CANDIDATE: same diagnostics at each switch')
raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
A = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs = [0, 2]
rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(A[i, 1], A[i, 0]))
cc = A[rings+hubs]
S = {}
for k in range(9):
    i, j = k, (k+1) % 9
    m = 0.5*(cc[i]+cc[j]); d = cc[j]-cc[i]; n = np.array([d[1], -d[0]])/np.linalg.norm(d)
    t0 = -(m @ n); s2 = 1 - m @ m
    for s in (1, -1):
        x = m + (t0+s*math.sqrt(t0*t0+s2))*n
        if abs(np.linalg.norm(x-cc[i])-np.linalg.norm(x-cc[j])) > 1e-9: continue
        if np.linalg.norm(x-cc[i])-min(np.linalg.norm(q-x) for q in cc) > 1e-9: continue
        S[k] = x
for k in [5]:
    P = S[k]
    print(' switch S_%d =' % k, np.round(P, 6))
    print('  signed angle at S between c_%d and c_%d = %.6f' % (k, k+1, math.atan2(cross(cc[k]-P, cc[k+1]-P), dot(cc[k]-P, cc[k+1]-P))))
    # the polygon edges
    u = S[(k-1) % 9]-P; v = S[(k+1) % 9]-P
    print('  signed angle(u,v) = %.6f   interior (pi - signed) = %.6f' % (math.atan2(cross(u, v), dot(u, v)), math.pi-math.atan2(cross(u, v), dot(u, v))))
    ci = cc[k]-P; cj = cc[(k+1) % 9]-P
    print('  signed(u,ci) = %.6f  signed(ci,cj) = %.6f  signed(cj,v) = %.6f  sum = %.6f'
          % (math.atan2(cross(u, ci), dot(u, ci)), math.atan2(cross(ci, cj), dot(ci, cj)),
             math.atan2(cross(cj, v), dot(cj, v)),
             math.atan2(cross(u, ci), dot(u, ci))+math.atan2(cross(ci, cj), dot(ci, cj))+math.atan2(cross(cj, v), dot(cj, v))))
    print('  unsigned T=%.6f L=%.6f apex=%.6f sum=%.6f' % (
        math.atan2(abs(cross(u, ci)), dot(u, ci)), math.atan2(abs(cross(cj, v)), dot(cj, v)),
        math.atan2(abs(cross(ci, cj)), dot(ci, cj)),
        math.atan2(abs(cross(u, ci)), dot(u, ci))+math.atan2(abs(cross(ci, cj)), dot(ci, cj))+math.atan2(abs(cross(cj, v)), dot(cj, v))))
