"""DEFINITIVE closure test, using exact Voronoi ridges.

For a 9-ring + 2-hub configuration:
 * switch S_k = the bisector endpoint of the ring pair (k,k+1) on |x|=1
   (the unique point of |x|=1 equidistant from both and nearest to all).
 * the Voronoi cell of ring k at S_k is a wedge between two outgoing ridges;
   its angle A_k = angle between the two ridge directions.
 * 2 b_k = angle at S_k between the two ring sites c_k, c_{k+1} (taking the
   direction INSIDE the partition, i.e. the sum of the two hub cell angles).
 * identity tested:   A_k + A_(k+1)?  no -- the exact statement is
      (angle between the two RIDGE directions at S_k, measured through the cell
       of c_k side) ... but the cleanest is:
      cell angle of c_k at S_k + cell angle of c_{k+1} at S_k + 2 b_k = 2 pi
   where the sum of the two hub cell angles at S_k equals 2 b_k - (that is the
   definition of b_k as the half-angle of the wedge between the two ring cells).
 * also test the closure form T_k + L_(k+1) + 2 b_k + (w_k+w_{k+1})/2 = pi where
   T_k = angle at S_k between the ridge towards S_(k-1) and the ray to c_k, etc.
"""
import numpy as np, math, json
from pathlib import Path
from scipy.spatial import Voronoi
ROOT = Path(__file__).resolve().parents[3]
R = 0.38

def load_saved():
    raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
    a = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
    hubs = [0, 2]
    rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(a[i, 1], a[i, 0]))
    return a[rings+hubs]

def switch_pt(points, i, j, tol=1e-9):
    m = 0.5*(points[i]+points[j]); d = points[j]-points[i]
    n = np.array([d[1], -d[0]])/np.linalg.norm(d)
    t0 = -(m @ n); s2 = 1 - m @ m
    if s2 < 0: return None
    ok = []
    for sgn in (+1, -1):
        x = m + (t0+sgn*math.sqrt(t0*t0+s2))*n
        di = np.linalg.norm(x-points[i]); dj = np.linalg.norm(x-points[j])
        if abs(di-dj) > tol: continue
        if di - min(np.linalg.norm(x-q) for q in points) > tol: continue
        ok.append(x)
    return ok[0] if len(ok) == 1 else None

def ang(u, v):
    return math.atan2(u[0]*v[1]-u[1]*v[0], float(u @ v))

def analyse(name, c, verbose=False):
    c = np.asarray(c, float)
    vor = Voronoi(c)
    # switches
    S = {}
    for k in range(9):
        x = switch_pt(c, k, (k+1) % 9)
        if x is None: return None
        S[k] = x
    thr = [math.atan2(S[k][1], S[k][0]) % (2*math.pi) for k in range(9)]
    order = sorted(range(9), key=lambda k: thr[k])
    ths = [thr[k] for k in order]
    w = [(ths[(m+1) % 9]-ths[m]) % (2*math.pi) for m in range(9)]
    # cell angles at each switch: gather the 4 nearest sites in angular order
    out = []
    for k in range(9):
        P = S[k]
        d = np.array([np.linalg.norm(P-q) for q in c])
        idx = list(np.argsort(d))
        near = idx[:4]
        # angular positions
        pos = sorted([(math.atan2((c[i]-P)[1], (c[i]-P)[0]) % (2*math.pi), int(i)) for i in near])
        # cell of site i is the wedge between its two angular neighbours in the partition:
        # the four cells tile 2pi, and a cell's angle = the angular gap between the
        # positions of its two ridge-neighbours.  For a 4-cell partition the gaps ARE
        # the cell angles (each cell occupies the sector between its own ray and the
        # next cell's ray in the opposite sense).  Concretely, the cells in angular
        # order are p0,p1,p2,p3 with gaps g0=p1-p0, ... and the cell of a site is the
        # gap *ending* at its ray.
        gaps = [(pos[(t+1) % 4][0]-pos[t][0]) % (2*math.pi) for t in range(4)]
        cellang = {pos[t][1]: gaps[t] for t in range(4)}
        A_i = cellang[k]; A_j = cellang[(k+1) % 9]
        hub_ids = [i for i in near if i >= 9]
        hub_sum = sum(cellang[i] for i in hub_ids)
        out.append((k, A_i, A_j, hub_sum, A_i+A_j+hub_sum))
    return S, w, order, out

if __name__ == '__main__':
    c = load_saved()
    res = analyse('saved', c)
    S, w, order, out = res
    print(' k   A_k        A_(k+1)    hubsum     total(2pi?)   w_k+w_(k+1)  T+L+apex+w/2-pi')
    for (k, Ai, Aj, hs, tot) in out:
        i, j = k, (k+1) % 9
        P = S[k]; Pm = S[(k-1) % 9]; Pp = S[(k+1) % 9]
        T = abs(ang(Pm-P, c[i]-P)); L = abs(ang(c[j]-P, Pp-P)); apex = abs(ang(c[i]-P, c[j]-P))
        wsum = w[order.index((k-1) % 9)] + w[order.index(k)]
        print('%2d %10.6f %10.6f %10.6f  %10.6f    %10.6f   %+.2e'
              % (k, Ai, Aj, hs, tot, wsum, T+L+apex+wsum/2-math.pi))
