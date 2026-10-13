"""Definitive check of the sector-triangle angle formulas and the closure pairing.

Sector triangle i: A = P_{i-1}, C = c_i, B = P_i;  a_i = angle at C,
u = |CA|, v = |CB|.
Claimed formulas (lead):  angle at A = atan2(v sin a, u - v cos a),
                          angle at B = atan2(u sin a, v - u cos a).
We compare BOTH formulas with the geometric angles computed by dot/cross, for
each sector, and then test the closure pairing.
"""
import numpy as np, math, json
from pathlib import Path
ROOT = Path('.').resolve().parents[2]
def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)
def ang(u, v): return math.atan2(abs(cross(u, v)), dot(u, v))
def turn(u, v): return math.atan2(abs(cross(u, v)), dot(u, v))

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

print('sector triangle i = (A=S_{i-1}, C=c_i, B=S_i)')
print(' i |  u     v      a     | atA(geo) atA(f1)  atA(f2) | atB(geo) atB(f1)  atB(f2)')
fA = {}; fB = {}
for i in range(9):
    A = S[(i-1) % 9]; B = S[i]; C = c[i]
    u = np.linalg.norm(C-A); v = np.linalg.norm(C-B); al = ang(A-C, B-C)
    atA_geo = ang(B-A, C-A); atB_geo = ang(A-B, C-B)
    f1 = math.atan2(v*math.sin(al), u - v*math.cos(al))
    f2 = math.atan2(u*math.sin(al), v - u*math.cos(al))
    fA[i] = atA_geo; fB[i] = atB_geo
    print('%2d | %.4f %.4f %.4f | %.6f %.6f %.6f | %.6f %.6f %.6f'
          % (i, u, v, al, atA_geo, f1, f2, atB_geo, f1, f2))
print()
print('=> f1 = atan2(v sin a, u - v cos a) is the angle at ... (see columns)')
print('=> f2 = atan2(u sin a, v - u cos a) is the angle at ...')
print()
print('CLOSURE pairings tested (all angles from geometry):')
cands = {
    'A: T_i + L_i + 2b_i + (w_{i-1}+w_i)/2': lambda i: fB[i] + fA[i] + ang(c[i]-S[i], c[(i+1) % 9]-S[i]) + (w[(i-1) % 9]+w[i])/2,
    'B: T_i + L_{i+1} + 2b_i + (w_i+w_{i+1})/2': lambda i: fB[i] + fA[(i+1) % 9] + ang(c[i]-S[i], c[(i+1) % 9]-S[i]) + (w[i]+w[(i+1) % 9])/2,
    'C: L_i + T_{i+1} + 2b_i + (w_{i-1}+w_i)/2': lambda i: fA[i] + fB[(i+1) % 9] + ang(c[i]-S[i], c[(i+1) % 9]-S[i]) + (w[(i-1) % 9]+w[i])/2,
    'D: L_i + L_{i+1} + 2b_i + (w_{i-1}+w_i)/2': lambda i: fA[i] + fA[(i+1) % 9] + ang(c[i]-S[i], c[(i+1) % 9]-S[i]) + (w[(i-1) % 9]+w[i])/2,
}
for name, f in cands.items():
    vals = [f(i) for i in range(9)]
    print('  %-46s max|val-pi| = %.3e' % (name, max(abs(v-math.pi) for v in vals)))
