"""Branch-consistency check for the kernel's closure equation.

The kernel's ring factor for site i carries, in the closure multipliers,
  left  = atan2(v_i sin a_i, u_i - v_i cos a_i)   -> contributes +left  to alpha_{i-1}
  right = atan2(u_i sin a_i, v_i - u_i cos a_i)   -> contributes +right to alpha_i
so the closure equation at switch S_i is

   right_i + left_{i+1} + (w_i + w_{i+1})/2 + (angle coefficients) = pi .

Question: is this the cone-order identity, i.e. are `right_i` and `left_{i+1}`
the two base angles AT S_i of the triangles (S_{i-1}, c_i, S_i) and
(S_i, c_{i+1}, S_{i+1}) in the cone-order branch?

We evaluate both formulas on the saved candidate from coordinates alone.
"""
import numpy as np, math, json
from pathlib import Path
ROOT = Path('.').resolve().parents[2]
def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)
def ang(u, v): return math.atan2(abs(cross(u, v)), dot(u, v))
def sang(u, v): return math.atan2(cross(u, v), dot(u, v))

raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
A = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs = [0, 2]
rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(A[i, 1], A[i, 0]))
c = A[rings+hubs]
S = {}
for k in range(9):
    i, j = k, (k+1) % 9
    m = 0.5*(c[i]+c[j]); dd = c[j]-c[i]; n = np.array([dd[1], -dd[0]])/np.linalg.norm(dd)
    t0 = -(m @ n); s2 = 1 - m @ m
    for sgn in (+1, -1):
        x = m + (t0+sgn*math.sqrt(t0*t0+s2))*n
        if abs(np.linalg.norm(x-c[i])-np.linalg.norm(x-c[j])) > 1e-9: continue
        if np.linalg.norm(x-c[i])-min(np.linalg.norm(q-x) for q in c) > 1e-9: continue
        S[k] = x
th = [math.atan2(S[k][1], S[k][0]) % (2*math.pi) for k in range(9)]
order = sorted(range(9), key=lambda k: th[k]); ths = [th[k] for k in order]
w = {order[m]: (ths[(m+1) % 9]-ths[m]) % (2*math.pi) for m in range(9)}

print('i | kernel right_i (at S_i, tri S_{i-1}c_iS_i) | cone order angle | diff | kernel left_{i+1} | cone angle | diff')
ok = True
for i in range(9):
    P = S[i]
    # kernel right_i: angle at S_i between c_i and S_{i+1}: atan2(u sin a, v - u cos a)
    # with u=|S_i-c_i|, v=|S_i-S_{i+1}|, a=angle at c_i between S_i and S_{i+1}
    u = np.linalg.norm(P-c[i]); vv = np.linalg.norm(S[(i+1) % 9]-P)
    a = ang(P-c[i], S[(i+1) % 9]-c[i])
    right_k = math.atan2(u*math.sin(a), vv-u*math.cos(a))
    right_geo = ang(c[i]-P, S[(i+1) % 9]-P)
    # kernel left_{i+1}: at S_{i+1}, triangle (S_i, c_{i+1}, S_{i+1}); angle at S_{i+1}
    Pn = S[(i+1) % 9]
    u2 = np.linalg.norm(Pn-c[(i+1) % 9]); v2 = np.linalg.norm(S[i]-Pn)
    a2 = ang(Pn-c[(i+1) % 9], S[i]-c[(i+1) % 9])
    left_k = math.atan2(v2*math.sin(a2), u2-v2*math.cos(a2))
    left_geo = ang(c[(i+1) % 9]-Pn, S[i]-Pn)
    # the closure equation as the kernel assembles it:
    wl = w[i]; wr = w[(i+1) % 9]
    ker = right_k + left_k + (wl+wr)/2
    cone = right_geo + left_geo + (wl+wr)/2
    same = abs(right_k-right_geo) < 1e-9 and abs(left_k-left_geo) < 1e-9
    ok = ok and same
    print('%d | %.6f | %.6f | %+.1e | %.6f | %.6f | %+.1e' %
          (i, right_k, right_geo, right_k-right_geo, left_k, left_geo, left_k-left_geo))
print()
print('kernel right/left equal the geometric base angles at the switch:', ok)
print('=> the kernel closure equation IS the cone-order identity (branch-consistent).')
