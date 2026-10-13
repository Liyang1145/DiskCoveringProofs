"""Read the switch vertex structure directly from scipy's Voronoi ridges.

For each ring pair (k,k+1) with switch S_k on |x|=1:
  * find the two Voronoi vertices of the pair's shared ridge (one is S_k),
  * get the ring's cell angle at S_k from the ridge directions, and
  * test  cell_angle(c_k) + cell_angle(c_(k+1)) + 2*b_k = 2 pi
    together with the equivalent closure form.
"""
import numpy as np, math, json
from pathlib import Path
from scipy.spatial import Voronoi
ROOT = Path(__file__).resolve().parents[3]

def load_saved():
    raw = json.loads((ROOT/'n11'/'upper'/'certified_object.json').read_text(encoding='utf-8-sig'))
    a = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
    hubs = [0, 2]
    rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(a[i, 1], a[i, 0]))
    return a[rings+hubs]

def ang(u, v):
    return math.atan2(u[0]*v[1]-u[1]*v[0], float(u @ v))

def analyse(c, verbose=True):
    c = np.asarray(c, float); n = len(c)
    vor = Voronoi(c)
    # ridge for each neighbour pair
    ridge = {}
    for (pp, vv) in zip(vor.ridge_points, vor.ridge_vertices):
        ridge[tuple(sorted(pp))] = vv
    S = {}
    for k in range(9):
        i, j = k, (k+1) % 9
        m = 0.5*(c[i]+c[j]); d = c[j]-c[i]
        nn = np.array([d[1], -d[0]])/np.linalg.norm(d)
        t0 = -(m @ nn); s2 = 1 - m @ m
        if s2 < 0: return None
        cand = []
        for sgn in (+1, -1):
            x = m + (t0+sgn*math.sqrt(t0*t0+s2))*nn
            di = np.linalg.norm(x-c[i]); dj = np.linalg.norm(x-c[j])
            if abs(di-dj) > 1e-9: continue
            if di - min(np.linalg.norm(x-q) for q in c) > 1e-9: continue
            cand.append(x)
        if len(cand) != 1: return None
        S[k] = cand[0]
    thr = [math.atan2(S[k][1], S[k][0]) % (2*math.pi) for k in range(9)]
    order = sorted(range(9), key=lambda k: thr[k]); ths = [thr[k] for k in order]
    w = [(ths[(m+1) % 9]-ths[m]) % (2*math.pi) for m in range(9)]
    rows = []
    for k in range(9):
        P = S[k]
        vd = vor.vertices - P
        dist = np.linalg.norm(vd, axis=1)
        # the other vertex of the ridge of pair (k,k+1) is the next-nearest voronoi vertex
        idx = np.argsort(dist)
        # cell angle of site k at P: use the 4 cells at P (nearest sites);
        # ridge directions from P:
        d = np.array([np.linalg.norm(P-q) for q in c])
        near = list(np.argsort(d))[:4]
        # cell of site i is bounded by ridges towards its neighbours; among the 4 cells
        # at P the "ridges" are the directions of the 4 edges; each edge lies between two
        # of the rays; the angular span of a cell = the gap between the rays of the two
        # sites bounding it.  Determine by simulation of the nearest-site at P + eps*dir:
        rays = {}
        for i in near:
            v = c[i]-P
            rays[i] = math.atan2(v[1], v[0]) % (2*math.pi)
        # boundaries of cell i: rotate from ray_i in both directions until the nearest
        # site changes; the change happens at the bisector with the neighbouring site.
        def cellsect(i, other):
            """direction (angle) of the ridge between cells i,other, from P outward/inward"""
            # bisector point of i,other: the direction from P is perpendicular to (c_i-c_other)
            dd = c[other]-c[i]
            return math.atan2(dd[1], dd[0]) + math.pi/2
        # find, for site i, the two nearest rays (angular neighbours)
        ray_sorted = sorted(rays.items(), key=lambda t: t[1])
        ang_of = {i: t for i, t in ray_sorted}
        pos = [t[1] for t in ray_sorted]
        A = {}
        for t in range(4):
            i_here = ray_sorted[t][0]
            prev = ray_sorted[(t-1) % 4][0]
            nxt = ray_sorted[(t+1) % 4][0]
            # cell of i_here is bounded by bisectors with prev and nxt
            b1 = cellsect(i_here, prev); b2 = cellsect(i_here, nxt)
            A[i_here] = abs(ang(np.array([math.cos(b1), math.sin(b1)]), np.array([math.cos(b2), math.sin(b2)])))
        Ai, Aj = A[k], A[(k+1) % 9]
        hs = sum(A[i] for i in near if i >= 9)
        b2 = abs(ang(c[k]-P, c[(k+1) % 9]-P))
        wsum = w[order.index((k-1) % 9)] + w[order.index(k)]
        T = abs(ang(S[(k-1) % 9]-P, c[k]-P)); L = abs(ang(c[(k+1) % 9]-P, S[(k+1) % 9]-P))
        rows.append((k, Ai, Aj, hs, Ai+Aj+hs, wsum, T+L+b2+wsum/2-math.pi))
    if verbose:
        print(' k      A_k     A_(k+1)   hubsum    total        wsum    resid_closure')
        for r in rows:
            print('%2d %9.6f %9.6f %9.6f %9.6f %9.6f  %+.2e' % r)
        print('max |total-2pi| =', max(abs(r[4]-2*math.pi) for r in rows))
        print('max |closure residual| =', max(abs(r[6]) for r in rows))
    return rows

if __name__ == '__main__':
    analyse(load_saved())
