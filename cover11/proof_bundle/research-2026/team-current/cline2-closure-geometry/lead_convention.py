"""EXACT convention check (lead's notation):
sector triangle i = (A=P_{i-1}, C=c_i, B=P_i), |CA|=R u_i, |CB|=R v_i, angle at C = a_i.
  L_i := angle at A ,  T_i := angle at B = pi - a_i - L_i .
Kernel closure equation at switch P_i:
  T_i + L_{i+1} + 2 b_i + (w_i + w_{i+1})/2 = pi .
Here L_{i+1} is the angle at A=P_i of the (i+1)-st sector triangle, i.e. at the
CURRENT switch. Verify numerically, coordinates only.
"""
import numpy as np, math, json
from pathlib import Path
ROOT = Path('.').resolve().parents[2]
def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)
def ang(u, v): return math.atan2(abs(cross(u, v)), dot(u, v))

raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
A_ = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs = [0, 2]
rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(A_[i, 1], A_[i, 0]))
c = A_[rings+hubs]
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

# sector triangle i: A = S_{i-1}, C = c_i, B = S_i
print(' i | L_i(formula) | L_i(geo at A) | T_i(formula) | T_i(geo at B) | a_i')
Lf = {}; Tf = {}
worstL = worstT = 0.0
for i in range(9):
    A = S[(i-1) % 9]; B = S[i]; C = c[i]
    u = np.linalg.norm(C-A)   # = R u_i
    v = np.linalg.norm(C-B)   # = R v_i
    a = ang(A-C, B-C)         # angle at C
    L_formula = math.atan2(v*math.sin(a), u - v*math.cos(a))
    L_geo = ang(B-A, C-A)
    T_formula = math.pi - a - L_formula
    T_geo = ang(A-B, C-B)
    worstL = max(worstL, abs(L_formula-L_geo)); worstT = max(worstT, abs(T_formula-T_geo))
    Lf[i] = L_formula; Tf[i] = T_formula
    print('%2d | %12.6f | %12.6f | %12.6f | %12.6f | %.6f' % (i, L_formula, L_geo, T_formula, T_geo, a))
print('max |L_formula - L_geo| = %.2e ; max |T_formula - T_geo| = %.2e' % (worstL, worstT))
print()
print('KERNEL CLOSURE:  T_i + L_{i+1} + 2b_i + (w_i+w_{i+1})/2 = pi')
worst = 0.0
for i in range(9):
    P = S[i]
    two_b = ang(c[i]-P, c[(i+1) % 9]-P)
    val = Tf[i] + Lf[(i+1) % 9] + two_b + (w[i]+w[(i+1) % 9])/2
    worst = max(worst, abs(val-math.pi))
    print('  i=%d  T=%8.5f  L_(i+1)=%8.5f  2b=%8.5f  wterm=%8.5f  sum=%.9f  diff=%+.1e'
          % (i, Tf[i], Lf[(i+1) % 9], two_b, (w[i]+w[(i+1) % 9])/2, val, val-math.pi))
print('worst |sum-pi| = %.3e' % worst)
