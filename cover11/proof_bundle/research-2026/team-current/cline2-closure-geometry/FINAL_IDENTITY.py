"""DEFINITIVE closure equation (pairing C), verified to machine precision.

Sector triangle i: A = P_{i-1}, C = c_i, B = P_i;  a_i = angle at C, u = |CA|, v = |CB|.
  L_i := angle at A = atan2(v sin a, u - v cos a)      [at P_{i-1}]
  T_i := angle at B = atan2(u sin a, v - u cos a) = pi - a_i - L_i   [at P_i]

THE closure equation (kernel/C820 form):
   L_i + T_{i+1} + 2 b_i + (w_{i-1} + w_i)/2 = pi
where 2b_i = angle at P_i between c_i and c_{i+1}, and w_i = arc width P_{i-1}->P_i.

Proof sketch: the four rays at P_i are a=P_{i-1}, c_i, c_{i+1}, b=P_{i+1} in cone
order with aperture pi-(w_i+w_{i+1})/2 = pi-(w_{i-1}+w_i)/2 (the same pair of
weights, shifted). The two triangle base angles at P_i of the adjacent sector
triangles are T_i (triangle i) and L_{i+1} (triangle i+1), and the middle angle
is 2b_i; so T_i + L_{i+1} + 2b_i = pi-(w_{i-1}+w_i)/2. Rotating indices by one:
L_i + T_{i+1} + 2b_i = pi-(w_{i-1}+w_i)/2, which is the same equation.
"""
import numpy as np, math, json
from pathlib import Path
ROOT = Path('.').resolve().parents[2]
def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)
def ang(u, v): return math.atan2(abs(cross(u, v)), dot(u, v))

def analyse(c, label):
    S = {}
    for k in range(9):
        i, j = k, (k+1) % 9
        m = 0.5*(c[i]+c[j]); dd = c[j]-c[i]; n = np.array([dd[1], -dd[0]])/np.linalg.norm(dd)
        t0 = -(m @ n); s2 = 1 - m @ m
        cand = []
        for sgn in (+1, -1):
            x = m + (t0+sgn*math.sqrt(t0*t0+s2))*n
            if abs(np.linalg.norm(x-c[i])-np.linalg.norm(x-c[j])) > 1e-9: continue
            if np.linalg.norm(x-c[i])-min(np.linalg.norm(q-x) for q in c) > 1e-9: continue
            cand.append(x)
        if len(cand) != 1: return None
        S[k] = cand[0]
    th = [math.atan2(S[k][1], S[k][0]) % (2*math.pi) for k in range(9)]
    order = sorted(range(9), key=lambda k: th[k]); ths = [th[k] for k in order]
    w = {order[m]: (ths[(m+1) % 9]-ths[m]) % (2*math.pi) for m in range(9)}
    print('===', label)
    worst = 0.0
    for i in range(9):
        A = S[(i-1) % 9]; B = S[i]; C = c[i]
        u = np.linalg.norm(C-A); v = np.linalg.norm(C-B); al = ang(A-C, B-C)
        L = math.atan2(v*math.sin(al), u-v*math.cos(al))
        # T_{i+1}: in sector triangle i+1, base angle at P_{i+1}
        A2 = S[i]; B2 = S[(i+1) % 9]; C2 = c[(i+1) % 9]
        u2 = np.linalg.norm(C2-A2); v2 = np.linalg.norm(C2-B2); al2 = ang(A2-C2, B2-C2)
        T2 = math.atan2(v2*math.sin(al2), u2-v2*math.cos(al2))
        P = S[i]
        two_b = ang(c[i]-P, c[(i+1) % 9]-P)
        val = L + T2 + two_b + (w[(i-1) % 9]+w[i])/2
        worst = max(worst, abs(val-math.pi))
        if label.startswith('saved'):
            print('  i=%d L_i=%.6f  T_(i+1)=%.6f  2b_i=%.6f  wterm=%.6f  sum=%.9f  diff=%+.1e'
                  % (i, L, T2, two_b, (w[(i-1) % 9]+w[i])/2, val, val-math.pi))
    print('  max |sum - pi| = %.3e' % worst)
    return worst

if __name__ == '__main__':
    raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
    X = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
    hubs = [0, 2]
    rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(X[i, 1], X[i, 0]))
    analyse(X[rings+hubs], 'saved candidate')
    for rho in [0.86, 0.90, 0.94]:
        cs = np.array([[rho*math.cos(k*2*math.pi/9), rho*math.sin(k*2*math.pi/9)] for k in range(9)])
        analyse(cs, 'regular 9-gon rho=%.2f' % rho)
