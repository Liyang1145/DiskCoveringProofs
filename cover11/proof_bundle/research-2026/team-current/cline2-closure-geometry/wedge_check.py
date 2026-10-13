"""Settle the wedge/ray-order question with exact arithmetic on the saved candidate.

For each switch P_i:
  u = P_{i-1} - P_i , v = P_{i+1} - P_i  (the two polygon edge rays)
  n = c_{i+1} - c_i
  test signs of  cross(u, w) for w in {v, c_i - P_i, c_{i+1} - P_i}
  and the angles of each ray relative to u.
"""
import numpy as np, math, json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]

def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v): return float(u @ v)
def aabs(u, v): return math.atan2(abs(cross(u, v)), dot(u, v))
def direction(u): return math.degrees(math.atan2(u[1], u[0])) % 360

raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
A = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs = [0, 2]
rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(A[i, 1], A[i, 0]))
c = A[rings+hubs]
print('ring norms:', np.round(np.linalg.norm(c[:9], axis=1), 9))
print('hub  norms:', np.round(np.linalg.norm(c[9:], axis=1), 9))
print('r-bound s = sqrt(1-r^2) with r = cover radius 0.37998385312:', math.sqrt(1-0.37998385312**2))

# switch table via nearest-site test
S = {}
for k in range(9):
    i, j = k, (k+1) % 9
    m = 0.5*(c[i]+c[j]); d = c[j]-c[i]
    n = np.array([d[1], -d[0]])/np.linalg.norm(d)
    t0 = -(m @ n); s2 = 1 - m @ m
    for sgn in (+1, -1):
        x = m + (t0+sgn*math.sqrt(t0*t0+s2))*n
        if abs(np.linalg.norm(x-c[i])-np.linalg.norm(x-c[j])) > 1e-9: continue
        if np.linalg.norm(x-c[i]) - min(np.linalg.norm(x-q) for q in c) > 1e-9: continue
        S[k] = x
print('switch radii:', np.round([np.linalg.norm(S[k]-c[k]) for k in range(9)], 12))
print()
print(' k | sign cross(u,v) | sign cross(u,ci-P) | sign cross(u,cj-P) | angle(u,v) | angle(u,ci-P) angle(ci-P,cj-P) angle(cj-P,v)')
for k in range(9):
    P = S[k]; u = S[(k-1) % 9]-P; v = S[(k+1) % 9]-P
    ci = c[k]-P; cj = c[(k+1) % 9]-P
    n = c[(k+1) % 9]-c[k]
    s1 = np.sign(cross(u, v)); s2 = np.sign(cross(u, ci)); s3 = np.sign(cross(u, cj))
    print('%2d | %+d | %+d | %+d | %8.4f | %8.4f %8.4f %8.4f' %
          (k, s1, s2, s3, aabs(u, v), aabs(u, ci), aabs(ci, cj), aabs(cj, v)))
    print('     check n.(u)=%+.6f  n.(v)=%+.6f  n.(ci)=%+.6f  n.(cj)=%+.6f  (|n|^2/2=%.6f)'
          % (dot(n, u), dot(n, v), dot(n, ci), dot(n, cj), dot(n, n)/2))
