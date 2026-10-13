"""FINAL: single-switch three-angle form of the closure identity, with all three
angles measured in the SAME (interior) direction, plus all supporting facts.

Identity:  T_k + 2b_k + L'_k + (w_{k-1}+w_k)/2 = pi
  T_k  = angle at S_k from ray S_k->S_{k-1} to ray S_k->c_k        (interior side)
  2b_k = angle at S_k from ray S_k->c_k     to ray S_k->c_{k+1}    (interior side)
  L'_k = angle at S_k from ray S_k->c_{k+1} to ray S_k->S_{k+1}    (interior side)
Equivalently the two-switch form used by the kernel:
  T_i + L_(i+1) + 2b_i + (w_i+w_{i+1})/2 = pi.
"""
import numpy as np, math, json
from pathlib import Path
ROOT = Path('.').resolve().parents[2]
def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)
def unsigned(u, v): return math.atan2(abs(cross(u, v)), dot(u, v))
def signed(u, v): return math.atan2(cross(u, v), dot(u, v))

raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
A = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs = [0, 2]
rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(A[i, 1], A[i, 0]))
c = A[rings+hubs]
S = {}
for k in range(9):
    i, j = k, (k+1) % 9
    m = 0.5*(c[i]+c[j]); d = c[j]-c[i]; n = np.array([d[1], -d[0]])/np.linalg.norm(d)
    t0 = -(m @ n); s2 = 1 - m @ m
    for sgn in (+1, -1):
        x = m + (t0+sgn*math.sqrt(t0*t0+s2))*n
        if abs(np.linalg.norm(x-c[i])-np.linalg.norm(x-c[j])) > 1e-9: continue
        if np.linalg.norm(x-c[i])-min(np.linalg.norm(q-x) for q in c) > 1e-9: continue
        S[k] = x
th = [math.atan2(S[k][1], S[k][0]) % (2*math.pi) for k in range(9)]
order = sorted(range(9), key=lambda k: th[k]); ths = [th[k] for k in order]
w = {order[m]: (ths[(m+1) % 9]-ths[m]) % (2*math.pi) for m in range(9)}

print('three-angle (single switch) form, all angles interior-directed:')
worst = 0.0
for k in range(9):
    P = S[k]
    u = S[(k-1) % 9]-P; x = c[k]-P; y = c[(k+1) % 9]-P; v = S[(k+1) % 9]-P
    # signed angles; all four rays in a cone of aperture < pi so the signs are common
    s1 = signed(u, x); s2 = signed(x, y); s3 = signed(y, v)
    same = (s1 > 0 and s2 > 0 and s3 > 0) or (s1 < 0 and s2 < 0 and s3 < 0)
    tot = abs(s1)+abs(s2)+abs(s3)
    theta = math.pi - (w[(k-1) % 9]+w[k])/2
    worst = max(worst, abs(tot-theta))
    print('  k=%d  T=%.6f 2b=%.6f L\'=%.6f  sum=%.6f  theta=%.6f  diff=%+.1e  same-direction=%s'
          % (k, abs(s1), abs(s2), abs(s3), tot, theta, tot-theta, same))
print('worst |sum - theta| = %.3e   (all interior-directed)\n' % worst)

print('two-switch kernel form:  T_i + L_(i+1) + 2b_i + (w_i+w_{i+1})/2 = pi')
worst2 = 0.0
for i in range(9):
    P = S[i]; T = unsigned(S[(i-1) % 9]-P, c[i]-P)
    b2 = unsigned(c[i]-P, c[(i+1) % 9]-P)
    Pn = S[(i+1) % 9]
    L1 = unsigned(c[(i+1) % 9]-Pn, S[(i+2) % 9]-Pn)
    val = T + L1 + b2 + (w[i]+w[(i+1) % 9])/2
    worst2 = max(worst2, abs(val-math.pi))
    print('  i=%d  T=%.6f L_%d=%.6f 2b=%.6f w-term=%.6f  sum=%.6f  diff=%+.1e'
          % (i, T, i+1, L1, b2, (w[i]+w[(i+1) % 9])/2, val, val-math.pi))
print('worst |(CL)-pi| = %.3e' % worst2)
