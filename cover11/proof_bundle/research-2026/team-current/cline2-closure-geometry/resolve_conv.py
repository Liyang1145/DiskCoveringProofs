"""Computational resolution: for each switch P_i, the three rays issued from P_i
that occur consecutively inside the polygon interior cone are
   r0 = P_{i-1}-P_i , r1 = c_i-P_i , r2 = c_{i+1}-P_i , r3 = P_{i+1}-P_i .
Verified (machine precision) cone identity:
   |s(r0,r1)| + |s(r1,r2)| + |s(r2,r3)| = theta_i = pi - (w_{i-1}+w_i)/2 .
Here we identify those three angles with the triangle base angles of the two
adjacent sector triangles, WITHOUT assuming which vertex they sit at, by
computing every candidate from coordinates and testing which naming makes the
kernel closure equation  T_i + L_{i+1} + 2b_i + (w_i + w_{i+1})/2 = pi  vanish.
"""
import numpy as np, math, json
from pathlib import Path
ROOT = Path('.').resolve().parents[2]
def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)
def ang(u, v): return math.atan2(abs(cross(u, v)), dot(u, v))

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

# candidate angle functions evaluated at a vertex P for a "site pair"
def angle_at(P, X, Y): return ang(X-P, Y-P)

print('For each switch P_i, list the two sector-triangle base angles AT P_i:')
print('  beta_i  = angle at P_i in sector triangle i   = angle(S_{i-1}-P_i, c_i-P_i)')
print('  gamma_i = angle at P_i in sector triangle i+1 = angle(c_{i+1}-P_i, S_{i+1}-P_i)')
print('  delta_i = angle at P_i between c_i and c_{i+1}')
print()
for i in range(9):
    P = S[i]
    beta = angle_at(P, S[(i-1) % 9], c[i])
    gamma = angle_at(P, c[(i+1) % 9], S[(i+1) % 9])
    delta = angle_at(P, c[i], c[(i+1) % 9])
    theta = math.pi-(w[(i-1) % 9]+w[i])/2
    print(' i=%d beta=%.6f gamma=%.6f delta=%.6f  beta+gamma+delta=%.6f theta=%.6f diff=%+.1e'
          % (i, beta, gamma, delta, beta+gamma+delta, theta, beta+gamma+delta-theta))
print()
print('Now the sector-triangle base angles computed by the kernel formulas')
print('  L_i = atan2(v sin a, u - v cos a) [triangle i: A=S_{i-1}, C=c_i, B=S_i]')
print('  T_i = atan2(u sin a, v - u cos a)')
for i in range(9):
    A = S[(i-1) % 9]; B = S[i]; C = c[i]
    u = np.linalg.norm(C-A); v = np.linalg.norm(C-B); al = angle_at(C, A, B)
    Lf = math.atan2(v*math.sin(al), u-v*math.cos(al))
    Tf = math.atan2(u*math.sin(al), v-u*math.cos(al))
    print(' i=%d u=%.6f v=%.6f a=%.6f | L_formula=%.6f (angle at A: %.6f) | T_formula=%.6f (angle at B: %.6f)'
          % (i, u, v, al, Lf, angle_at(A, B, C), Tf, angle_at(B, A, C)))
