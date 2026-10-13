"""Final convention (lead's notation, correctly applied):

sector triangle i = (A=P_{i-1}, C=c_i, B=P_i); angle at C = a_i.
Formulas:  angle at A = atan2(v sin a, u - v cos a)   [u=|CA|, v=|CB|]
           angle at B = atan2(u sin a, v - u cos a) = pi - a_i - (angle at A).

Kernel closure at switch P_i:
   T_i + L_{i+1} + 2 b_i + (w_i + w_{i+1})/2 = pi
with  T_i := angle at B=P_i of sector triangle i   (at the current switch)
      L_{i+1} := angle at A=P_i of sector triangle i+1 (also at the current switch)
      2 b_i := angle at P_i between the rays to c_i and c_{i+1}.
Verify on the saved candidate and on a regular nonagon.
"""
import numpy as np, math, json
from pathlib import Path
ROOT = Path('.').resolve().parents[2]
def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)
def ang(u, v): return math.atan2(abs(cross(u, v)), dot(u, v))

def load_saved():
    raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
    X = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
    hubs = [0, 2]
    rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(X[i, 1], X[i, 0]))
    return X[rings+hubs]

def switches(c):
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
    return S

def widths(S):
    th = [math.atan2(S[k][1], S[k][0]) % (2*math.pi) for k in range(9)]
    order = sorted(range(9), key=lambda k: th[k]); ths = [th[k] for k in order]
    return {order[m]: (ths[(m+1) % 9]-ths[m]) % (2*math.pi) for m in range(9)}

def sector_angles(c, S):
    """T_i (at B=S_i) and L_i (at A=S_{i-1}) of sector triangle i, plus a_i."""
    T = {}; L = {}; a = {}
    for i in range(9):
        A = S[(i-1) % 9]; B = S[i]; C = c[i]
        u = np.linalg.norm(C-A); v = np.linalg.norm(C-B)
        al = ang(A-C, B-C)
        L[i] = math.atan2(v*math.sin(al), u - v*math.cos(al))   # angle at A
        T[i] = math.atan2(u*math.sin(al), v - u*math.cos(al))   # angle at B
        a[i] = al
    return T, L, a

def test(name, c, S):
    w = widths(S); T, L, a = sector_angles(c, S)
    print('===', name)
    worst = 0.0
    for i in range(9):
        P = S[i]
        two_b = ang(c[i]-P, c[(i+1) % 9]-P)
        val = T[i] + L[(i+1) % 9] + two_b + (w[i]+w[(i+1) % 9])/2
        worst = max(worst, abs(val-math.pi))
        print('  i=%d T_i=%8.5f L_(i+1)=%8.5f 2b_i=%8.5f wterm=%8.5f sum=%.9f diff=%+.1e'
              % (i, T[i], L[(i+1) % 9], two_b, (w[i]+w[(i+1) % 9])/2, val, val-math.pi))
    print('  worst |sum-pi| = %.3e' % worst)
    # also: triangle sums
    err = max(abs(T[i]+L[i]+a[i]-math.pi) for i in range(9))
    print('  max |T_i+L_i+a_i-pi| = %.2e' % err)
    return worst

if __name__ == '__main__':
    c = load_saved(); S = switches(c)
    test('saved candidate', c, S)
    print()
    # regular 9-gon with a hub pair at the origin (not a cover, but tests the identity)
    K = np.array([[math.cos(k*2*math.pi/9), math.sin(k*2*math.pi/9)] for k in range(9)])
    S2 = {}
    for k in range(9):
        A = K[k]; B = K[(k+1) % 9]
        m = 0.5*(A+B); dd = B-A; n = np.array([dd[1], -dd[0]])/np.linalg.norm(dd)
        t0 = -(m @ n); s2 = 1 - m @ m
        for sgn in (+1, -1):
            x = m + (t0+sgn*math.sqrt(t0*t0+s2))*n
            if np.linalg.norm(x-A) < 1:   # the inward crossing
                S2[k] = x
    rad = 0.9
    c2 = np.array([[rad*math.cos(k*2*math.pi/9), rad*math.sin(k*2*math.pi/9)] for k in range(9)])
    test('regular nonagon (9-gon + 9 sites at 0.9, no hubs)', c2, S2)
