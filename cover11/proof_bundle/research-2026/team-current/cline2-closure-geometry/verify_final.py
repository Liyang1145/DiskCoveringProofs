"""Angle-convention-free verification using the fact that all vertices of K are
on the unit circle in CCW order: the interior angle at P_k equals
   pi' = pi - (w_{k-1}+w_k)/2      (exact, inscribed angle theorem)
and the interior sector is the one swept CLOCKWISE from u=P_{k-1}-P_k to v=P_{k+1}-P_k.

We therefore measure every interior angle as the clockwise sweep and check
identity A and the kernel's closure form CL."""
import numpy as np, math, json
from pathlib import Path
ROOT = Path('.').resolve().parents[2]
def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)
def cw(u, v):   # clockwise angle from u to v, in (0, 2pi]
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
w = {}
for m in range(9):
    w[(order[m], order[(m+1) % 9])] = (ths[(m+1) % 9]-ths[m]) % (2*math.pi)

print(' k | A_resid   CL_resid   alpha_k   interior_check')
maxA = maxCL = 0.0
for k in range(9):
    P = S[k]; Pm = S[(k-1) % 9]; Pp = S[(k+1) % 9]
    u = Pm-P; v = Pp-P; ci = c[k]-P; cj = c[(k+1) % 9]-P
    Tk = cw(u, ci); apex = cw(ci, cj); Lk = cw(cj, v)
    wl = w[((k-1) % 9, k)]; wr = w[(k, (k+1) % 9)]
    A_res = Tk + apex + Lk - (math.pi - (wl+wr)/2)
    # L_{k+1} measured at S_{k+1}: clockwise from c_{k+1}-S_{k+1} to S_{k+2}-S_{k+1}
    Pn = S[(k+1) % 9]
    Lk1 = cw(c[(k+1) % 9]-Pn, S[(k+2) % 9]-Pn)
    w2 = w[(k, (k+1) % 9)]; w3 = w[((k+1) % 9, (k+2) % 9)]
    CL_res = Tk + Lk1 + apex + (w2+w3)/2 - math.pi
    alpha_k = math.pi - (Tk + Lk) if (Tk+Lk) < math.pi else -(math.pi - (Tk+Lk))
    maxA = max(maxA, abs(A_res)); maxCL = max(maxCL, abs(CL_res))
    print('%2d | %+.2e  %+.2e  %+.6f   interior=%.6f pi-(w+w)/2=%.6f' %
          (k, A_res, CL_res, alpha_k, Tk+apex+Lk, math.pi-(wl+wr)/2))
print('max |A| = %.3e   max |CL| = %.3e' % (maxA, maxCL))
