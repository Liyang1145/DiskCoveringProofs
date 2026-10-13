"""Decide the exact closure convention by brute force on the saved candidate:
print every candidate combination of angles; find which one is identically 0."""
import numpy as np, math, json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
R = 0.38

def ang(u, v):
    return math.atan2(u[0]*v[1]-u[1]*v[0], float(u @ v))

def angabs(u, v):
    c = float(u @ v)/np.linalg.norm(u)/np.linalg.norm(v)
    return math.acos(max(-1, min(1, c)))

raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
a = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
hubs = [0, 2]
rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(a[i, 1], a[i, 0]))
c = a[rings + hubs]
print('ring norms', np.round(np.linalg.norm(c[:9], axis=1), 6))

# switches: point on |x|=1 on the bisector of (c_i,c_{i+1}) nearest to all sites
def switch(c0, c1, others):
    m = 0.5*(c0+c1); d = c1-c0; n = np.array([d[1], -d[0]])/np.linalg.norm(d)
    t0 = -(m @ n); s2 = 1 - m @ m
    out = []
    for sgn in (+1, -1):
        x = m + (t0 + sgn*math.sqrt(t0*t0+s2))*n
        othersd = min(np.linalg.norm(x-q) for q in others)
        out.append((x, np.linalg.norm(x-c0), othersd))
    return out

S = []
for k in range(9):
    i, j = k, (k+1) % 9
    cand = switch(c[i], c[j], c)
    ok = [t for t in cand if t[1] <= t[2] + 1e-9]
    S.append(ok[0][0])
S = np.array(S)
print('switch radii |P-c_i|:', np.round([np.linalg.norm(S[k]-c[k]) for k in range(9)], 12))
print('|P|:', np.round([np.linalg.norm(x) for x in S], 12))

# arc widths from the ray angles
th = [math.atan2(x[1], x[0]) % (2*math.pi) for x in S]
# find orientation: the polygon K is |x|<=1 inscribed 9-gon through S in angular order
order = sorted(range(9), key=lambda k: th[k])
th_s = [th[k] for k in order]
w = [(th_s[(m+1) % 9] - th_s[m]) % (2*math.pi) for m in range(9)]
print('widths', np.round(w, 9), 'sum', sum(w))

# for each switch k (between c_k and c_{k+1}) the two adjacent switches are
# S[k-1] (between c_{k-1},c_k) and S[k+1]
print()
print(' k   T_int   T_code  L_int  L_code   2b_full  2b_cell  chord(closing)  resid_code  resid_int  resid_alt')
for k in range(9):
    i, j = k, (k+1) % 9
    P = S[k]; Pm = S[(k-1) % 9]; Pp = S[(k+1) % 9]
    dir_prev = Pm - P; dir_next = Pp - P
    to_i = c[i] - P; to_j = c[j] - P
    T_int = angabs(dir_prev, to_i)                       # interior angle at P in tri(prev,c_i,P)
    T_code = ang(dir_prev, to_i)
    L_int = angabs(to_j, dir_next)
    L_code = ang(to_i, dir_next)                          # what my earlier script used
    apex_full = angabs(to_i, to_j)
    apex_code = ang(to_i, to_j)
    # chords
    chord_dir = Pp - P
    # cell angle: 2b from the Voronoi geometry
    d = np.linalg.norm(c[j]-c[i]); rho = np.linalg.norm(P-c[i])
    b = math.asin(min(1, d/(2*rho)))
    wl = next(w[m] for m in range(9) if order[m] == (k-1) % 9)
    wr = next(w[m] for m in range(9) if order[m] == k)
    resid_code = T_int + L_int + apex_code + (wl+wr)/2 - math.pi
    print('%2d %8.5f %8.5f %7.5f %7.5f %8.5f %8.5f %8.5f  %11.3e' % (
        k, T_int, T_code, L_int, L_code, apex_full, 2*apex_code, angabs(to_i, chord_dir)-L_int, resid_code))
