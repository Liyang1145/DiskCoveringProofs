"""Decide EXACTLY which angle equation vanishes on genuine configurations, by
brute force over the natural candidates (no hand algebra).

Definitions from coordinates:
  sector i: A=S_{i-1}, C=c_i, B=S_i;  angles: atA=atan2(v sin a,u-v cos a) [call LA_i],
            atB=atan2(u sin a,v-u cos a) [call LB_i], a_i at C.
  2*bi_in := angle at S_i between (c_i-S_i),(c_{i+1}-S_i) measured INSIDE the
             switch polygon (the cone order: it is < pi only when the ordering
             puts the two site rays inside; we take the value in (0,2pi) that
             makes T+2b+L = theta).
  theta_i = pi - (w_{i-1}+w_i)/2  (interior angle of the switch polygon at S_i).
Candidates tested for "= pi":
  A:  LB_i + LA_{i+1} + (bi at S_i) + (w_{i-1}+w_i)/2
  B:  LB_i + LA_{i+1} + (bi at S_i) + (w_i+w_{i+1})/2
  C:  LA_i + LB_{i+1} + ... etc.
"""
import numpy as np, math, json, itertools
from pathlib import Path
ROOT = Path('.').resolve().parents[2]
def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)
def ang(u, v): return math.atan2(abs(cross(u, v)), dot(u, v))
def sang(u, v): return math.atan2(cross(u, v), dot(u, v))

raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
X = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs = [0, 2]
rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(X[i, 1], X[i, 0]))
c = X[rings+hubs]
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

LA = {}; LB = {}; alpha = {}
for i in range(9):
    A = S[(i-1) % 9]; B = S[i]; C = c[i]
    u = np.linalg.norm(C-A); v = np.linalg.norm(C-B); al = ang(A-C, B-C)
    LA[i] = math.atan2(v*math.sin(al), u-v*math.cos(al))
    LB[i] = math.atan2(u*math.sin(al), v-u*math.cos(al))
    alpha[i] = al
    # sanity: LA must be the angle at A
    assert abs(LA[i]-ang(B-A, C-A)) < 1e-12, (i, LA[i], ang(B-A, C-A))
    assert abs(LB[i]-ang(A-B, C-B)) < 1e-12, (i, LB[i], ang(A-B, C-B))

# the middle angle at S_i between the two site rays, in the cone-order sense:
def mid(i):
    P = S[i]; s1 = sang(S[(i-1) % 9]-P, c[i]-P); s2 = sang(c[i]-P, c[(i+1) % 9]-P)
    return abs(s1)+abs(s2)+abs(sang(c[(i+1) % 9]-P, S[(i+1) % 9]-P)) - abs(sang(S[(i-1) % 9]-P, S[(i+1) % 9]-P))
def mid2(i):
    """angle at S_i between the two site rays, taking the branch that fits the cone"""
    P = S[i]
    a1 = ang(c[i]-P, c[(i+1) % 9]-P)
    return a1

print('cheking: theta_i = T_i + mid_i + L_i at the SAME switch, theta_i = pi-(w_{i-1}+w_i)/2')
print(' i | LB_i   LA_i   mid_i  | LB_i+LA_i+mid_i | theta_i | diff')
for i in range(9):
    theta = math.pi-(w[(i-1) % 9]+w[i])/2
    # the cone angles at S_i are: at S_{i-1}? No: rays at S_i are S_{i-1}, c_i, c_{i+1}, S_{i+1}
    P = S[i]
    t1 = ang(c[i]-P, S[(i+1) % 9]-P)         # = LB_i  (angle at B=S_i in sector i)
    t2 = ang(S[(i-1) % 9]-P, c[i]-P)         # = LA_{i+1}? angle at A=S_i in sector i+1
    t3 = ang(c[i]-P, c[(i+1) % 9]-P)         # between the two sites (unsigned)
    # the cone identity verified earlier: three consecutive rays sum to theta
    s = sang(S[(i-1) % 9]-P, c[i]-P)
    sm = sang(c[i]-P, c[(i+1) % 9]-P)
    s3 = sang(c[(i+1) % 9]-P, S[(i+1) % 9]-P)
    tot = abs(s)+abs(sm)+abs(s3)
    print('%2d | %.5f %.5f %.5f | %.6f | %.6f | %+.1e  (LB_i=%.6f LA_i+1=%.6f t3=%.6f)'
          % (i, LB[i], LA[i], t3, abs(s)+abs(sm)+abs(s3), theta, tot-theta,
             t1, t2, t3))
