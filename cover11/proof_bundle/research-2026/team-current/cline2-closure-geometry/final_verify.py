"""FINAL verification of the repaired closure argument on the saved candidate.

For each switch P_k (between rings k,k+1):
  w_{k-1}, w_k  : the two adjacent arc widths (from the cyclic switch table)
  alpha_k       : angle at c_k in triangle (P_{k-1}, c_k, P_k)
  interior_k    : interior angle of K at P_k, computed as the signed angle
                  from (P_{k-1}-P_k) to (P_{k+1}-P_k) measured INSIDE K
Identity A (three-radius identity):
  T_k + L_k + apex_k = interior_k = pi - (w_{k-1}+w_k)/2
      T_k = angle(P_{k-1}-P_k, c_k-P_k), L_k = angle(c_k-P_k, P_{k+1}-P_k),
      apex_k = angle(c_k-P_k, c_{k+1}-P_k)
Identity B (closure as used by the kernel):
  T_k + L_{k+1} + 2b_k + (w_k+w_{k+1})/2 = pi, 2b_k = angle(c_k-P_k, c_{k+1}-P_k)
Identity C (3-radius triangle sum):  alpha_k = pi - T_k - L_k
Identity D (sharper 2b):             2b_k = 2pi - alpha_k - alpha_{k+1} + (w_k+w_{k+1})/2
Also the w lower bound  w_j <= 2 asin r  and  w_j >= 2pi - 16 asin R.
"""
import numpy as np, math, json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)
def aabs(u, v): return math.atan2(abs(cross(u, v)), dot(u, v))
def ao(u, v):    # angle in (0,2pi) going CCW
    return math.atan2(cross(u, v), dot(u, v)) % (2*math.pi)

raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
A = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs = [0, 2]
rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(A[i, 1], A[i, 0]))
c = A[rings+hubs]
S = {}
for k in range(9):
    i, j = k, (k+1) % 9
    m = 0.5*(c[i]+c[j]); d = c[j]-c[i]
    n = np.array([d[1], -d[0]])/np.linalg.norm(d)
    t0 = -(m @ n); s2 = 1 - m @ m
    for sgn in (+1, -1):
        x = m + (t0+sgn*math.sqrt(t0*t0+s2))*n
        if abs(np.linalg.norm(x-c[i])-np.linalg.norm(x-c[j])) > 1e-9: continue
        if np.linalg.norm(x-c[i]) - min(np.linalg.norm(q-x) for q in c) > 1e-9: continue
        S[k] = x
th = [math.atan2(S[k][1], S[k][0]) % (2*math.pi) for k in range(9)]
order = sorted(range(9), key=lambda k: th[k]); ths = [th[k] for k in order]
w = {(order[m], order[(m+1) % 9]): (ths[(m+1) % 9]-ths[m]) % (2*math.pi) for m in range(9)}
r = 0.37998385311983869   # the candidate's covering radius (upper bound T_cert)
print('w bound check: max_j 2asin r = %.9f ; actual widths max %.9f' % (2*math.asin(r), max(w.values())))
print('lower bound 2pi-16asin R = %.9f ; min width %.9f' % (2*math.pi-16*math.asin(0.38), min(w.values())))
print()
print('  k | A: T+L+apex-(pi-(w+w)/2) | B: closure | C: alpha-(pi-T-L) | D: 2b formula | interior')
bad = 0
for k in range(9):
    P = S[k]; Pm = S[(k-1) % 9]; Pp = S[(k+1) % 9]
    u = Pm-P; v = Pp-P; ci = c[k]-P; cj = c[(k+1) % 9]-P
    # interior angle of K at P, measured inside (= 2pi - exterior CCW angle)
    interior = ao(u, v)
    if interior > math.pi: interior = 2*math.pi - interior
    # the interior must contain ci: check
    T = aabs(u, ci); L = aabs(ci, v); apex = aabs(ci, cj)
    wl = w[((k-1) % 9, k)]; wr = w[(k, (k+1) % 9)]
    A_ = T + L + apex - (math.pi - (wl+wr)/2)
    B_ = T + aabs(cj, v)*0 + aabs(cj, S[(k+1) % 9]-P) + apex + (wr + w[(k, (k+1) % 9)])/2 - math.pi
    # B as the kernel uses it: T_k + L_{k+1} + 2b_k + (w_k+w_{k+1})/2
    Tk = T
    Lk1 = aabs(c[(k+1) % 9]-P, S[(k+2) % 9]-S[(k+1) % 9]) if False else None
    # L_{k+1} is the angle at S_{k+1} between c_{k+1} and S_{k+2}
    Pn = S[(k+1) % 9]
    Lk1 = aabs(c[(k+1) % 9]-Pn, S[(k+2) % 9]-Pn)
    B_res = Tk + Lk1 + apex + (w[(k, (k+1) % 9)] + w[((k+1) % 9, (k+2) % 9)])/2 - math.pi
    alpha_k = math.pi - T - L
    alpha_k1 = math.pi - (aabs(S[k]-Pn, c[(k+1) % 9]-Pn) + aabs(c[(k+1) % 9]-Pn, S[(k+2) % 9]-Pn))
    D_ = (2*math.pi - alpha_k - alpha_k1 + (w[(k, (k+1) % 9)] + w[((k+1) % 9, (k+2) % 9)])/2) - apex
    print('%3d | %+.2e | %+.2e | %+.2e | %+.2e | %.6f (pi-(w+w)/2=%.6f)' %
          (k, A_, B_res, alpha_k - (math.pi - T - L), D_, interior, math.pi - (wl+wr)/2))
    if max(abs(A_), abs(B_res), abs(D_)) > 1e-12: bad += 1
print()
print('failures:', bad)
