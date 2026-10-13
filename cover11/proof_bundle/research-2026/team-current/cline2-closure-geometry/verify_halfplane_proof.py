"""Explicit verification of the CONE ORDER and DOMINANCE facts used by the lead's
halfplane proof (not residual-based):

At each switch P (=P_i, with a=P_{i-1}, b=P_{i+1}, c=c_i, d=c_{i+1}):
  1. all four rays a-P, c-P, d-P, b-P lie in the closed cone at P;
  2. they are in the cyclic order a, c, d, b (all four signed turns in (0,2pi));
  3. the Voronoi dominance inequalities hold:
        (d-c).(a-P) <= 0 <= (d-c).(b-P)      [needs "a in cl(V(c))"]
        |a-c| <= |a-d|, |b-d| <= |b-c|
  4. theta = pi - (w_i+w_{i+1})/2 equals the sum T_i + 2b_i + L_{i+1}.
"""
import numpy as np, math, json
from pathlib import Path
ROOT = Path('.').resolve().parents[2]
def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)
def turn(u, v):  # CCW angle from u to v in [0,2pi)
    return math.atan2(cross(u, v), dot(u, v)) % (2*math.pi)

def unsigned(u, v):  # ordinary angle in [0,pi]
    return math.atan2(abs(cross(u, v)), dot(u, v))

def cw(u, v):  # CW angle from u to v in [0,2pi)
    return (-math.atan2(cross(u, v), dot(u, v))) % (2*math.pi)

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

print(' k | T=turn(a,c) 2b=turn(c,d) L=turn(d,b) | orientation | sum-theta | dom_a dom_b | gap_ac gap_bd')
ok = True
for k in range(9):
    P = S[k]; a = S[(k-1) % 9]; b = S[(k+1) % 9]
    ci = c[k]; cj = c[(k+1) % 9]
    u = a-P; vv = b-P; cc = ci-P; dd = cj-P
    # angle from u to cc, measured in the direction (CW or CCW) that stays < pi
    if unsigned(u, cc) < math.pi and cw(u, cc) < math.pi:
        pass
    def pick(x, y):
        """the directed angle from x to y along the short way (< pi); return (value, sense)"""
        s = math.atan2(cross(x, y), dot(x, y))
        if abs(s) <= math.pi/2 or abs(s) <= math.pi:  # short way is |s| only if |s| = unsigned
            pass
        return s
    s_ac = math.atan2(cross(u, cc), dot(u, cc))
    s_cd = math.atan2(cross(cc, dd), dot(cc, dd))
    s_db = math.atan2(cross(dd, vv), dot(dd, vv))
    # all three must have the same sign; then their absolute values sum to theta
    same = (s_ac > 0 and s_cd > 0 and s_db > 0) or (s_ac < 0 and s_cd < 0 and s_db < 0)
    theta = math.pi - (w[(k-1) % 9] + w[k])/2
    ssum = abs(s_ac) + abs(s_cd) + abs(s_db)
    n = cj-ci
    dom_a = dot(n, u); dom_b = dot(n, vv)
    g1 = np.linalg.norm(a-ci)**2 - np.linalg.norm(a-cj)**2
    g2 = np.linalg.norm(b-cj)**2 - np.linalg.norm(b-ci)**2
    good = (same and abs(ssum-theta) < 1e-12 and dom_a <= 1e-12 and dom_b >= -1e-12
            and g1 <= 1e-12 and g2 <= 1e-12)
    ok = ok and good
    print('%2d | %+.5f %+.5f %+.5f | %s | %+.2e | %+.1e %+.1e | %+.1e %+.1e  %s'
          % (k, s_ac, s_cd, s_db, 'same' if same else 'MIXED', ssum-theta, dom_a, dom_b, g1, g2,
             'OK' if good else 'FAIL'))
print()
print('ALL CONE-ORDER + DOMINANCE FACTS VERIFIED:', ok)
print()
print('explicit check that the closure uses T_i + 2b_i + L_(i+1):')
for k in [0, 5]:
    P = S[k]; a = S[(k-1) % 9]; b = S[(k+1) % 9]
    T = turn(a-P, c[k]-P); two_b = turn(c[k]-P, c[(k+1) % 9]-P)
    # L_{k+1} at S_{k+1}: from c_{k+1}-S_{k+1} to S_{k+2}-S_{k+1}
    Pn = S[(k+1) % 9]
    L = turn(c[(k+1) % 9]-Pn, S[(k+2) % 9]-Pn)
    rhs = math.pi - (w[k]+w[(k+1) % 9])/2
    print('  k=%d: T=%.6f 2b=%.6f L=%.6f  T+2b+L=%.6f  pi-(w+w)/2=%.6f  diff=%+.1e'
          % (k, T, two_b, L, T+two_b+L, rhs, T+two_b+L-rhs))
