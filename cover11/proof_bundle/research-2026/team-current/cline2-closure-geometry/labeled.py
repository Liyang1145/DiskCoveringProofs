"""Labeled diagnostic: all candidate angles at a switch, computed once, so the
conventions stop being ambiguous."""
import numpy as np, math, json
from pathlib import Path
ROOT = Path('.').resolve().parents[2]
def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)
def ang(u, v): return math.atan2(abs(cross(u, v)), dot(u, v))
def sang(u, v): return math.atan2(cross(u, v), dot(u, v))
def d(u): return math.degrees(math.atan2(u[1], u[0])) % 360

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

k = 5
P = S[k]; a = S[(k-1) % 9]; b = S[(k+1) % 9]
ci = c[k]; cj = c[(k+1) % 9]
print('k =', k)
print('  P=%s  a=%s  b=%s' % (np.round(P, 5), np.round(a, 5), np.round(b, 5)))
print('  c_%d=%s  c_%d=%s' % (k, np.round(ci, 5), k+1, np.round(cj, 5)))
print('  |P-a|=%.6f |P-b|=%.6f |P-ci|=%.6f |P-cj|=%.6f' %
      (np.linalg.norm(P-a), np.linalg.norm(P-b), np.linalg.norm(P-ci), np.linalg.norm(P-cj)))
print('  ray directions: P->a %.3f  P->ci %.3f  P->cj %.3f  P->b %.3f' %
      (d(a-P), d(ci-P), d(cj-P), d(b-P)))
print('  unsigned angles: <a,ci>=%.6f  <ci,cj>=%.6f  <cj,b>=%.6f  <a,b>=%.6f'
      % (ang(a-P, ci-P), ang(ci-P, cj-P), ang(cj-P, b-P), ang(a-P, b-P)))
print('  signed angles:   <a,ci>=%+.6f <ci,cj>=%+.6f <cj,b>=%+.6f <a,b>=%+.6f'
      % (sang(a-P, ci-P), sang(ci-P, cj-P), sang(cj-P, b-P), sang(a-P, b-P)))
print('  w_%d=%.6f w_%d=%.6f  (w+w)/2=%.6f  pi-(w+w)/2=%.6f'
      % (k-1, w[(k-1) % 9], k, w[k], (w[(k-1) % 9]+w[k])/2, math.pi-(w[(k-1) % 9]+w[k])/2))
# triangle (a, ci, P) and (P, cj, b)
T = ang(a-P, ci-P); alpha = ang(a-ci, P-ci); L_a = ang(P-a, ci-a)
print('  triangle (a,ci,P):  at P %.6f  at ci(alpha_k) %.6f  at a %.6f  sum %.6f' % (T, alpha, L_a, T+alpha+L_a))
alpha2 = ang(P-cj, b-cj); Lb = ang(P-b, cj-b)
print('  triangle (P,cj,b):  at P %.6f  at cj(alpha_%d) %.6f  at b %.6f  sum %.6f'
      % (ang(cj-P, b-P), k+1, alpha2, Lb, ang(cj-P, b-P)+alpha2+Lb))
# upstream triangle (a_prev, ci, P_k)... use k-1 triangle (S_{k-2}, c_{k-1}, S_{k-1})
# the closure equation at k involves T_k and the L of the NEXT switch
Pn = S[(k+1) % 9]
L_next = ang(cj-Pn, S[(k+2) % 9]-Pn)
alpha_next = ang(S[k]-cj, Pn-cj)
raise SystemExit if False else None
print()
print('  kernel-style ingredients:  T_k=%.6f  2b_k=<ci,cj>=%.6f  L_(k+1)=%.6f  (w_k+w_(k+1))/2=%.6f'
      % (T, ang(ci-P, cj-P), L_next, (w[k]+w[(k+1) % 9])/2))
print('     T_k + 2b_k + L_(k+1) + (w_k+w_(k+1))/2 = %.6f   (pi = %.6f)'
      % (T + ang(ci-P, cj-P) + L_next + (w[k]+w[(k+1) % 9])/2, math.pi))
print('  alternative: T_k + L_k + 2b_k + (w_(k-1)+w_k)/2 = %.6f'
      % (T + ang(cj-P, b-P) + ang(ci-P, cj-P) + (w[(k-1) % 9]+w[k])/2))
print('  measured: <a,b>=%.6f  and  <a,ci>+<ci,cj>+<cj,b>=%.6f'
      % (ang(a-P, b-P), ang(a-P, ci-P)+ang(ci-P, cj-P)+ang(cj-P, b-P)))
