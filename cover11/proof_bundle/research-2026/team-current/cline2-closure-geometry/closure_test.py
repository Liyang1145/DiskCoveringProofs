"""Independent audit: is the local boundary cyclic closure identity
   T_i + L_(i+1) + 2 b_i + (w_i + w_(i+1))/2 = pi
an exact identity for every genuine inward-root 9-ring+2-hub unit-disk cover?

Coordinates-only recomputation of: Voronoi cells / owned arcs / switches / closure.
Float diagnostics; does not import any lead helper.
"""
import numpy as np, math, json, sys
from pathlib import Path
from scipy.spatial import Delaunay, ConvexHull

ROOT = Path(__file__).resolve().parents[3]
P = Path(__file__).parent
R = 0.38

def ang(u, v):
    c = float(u @ v)/np.linalg.norm(u)/np.linalg.norm(v)
    return math.acos(max(-1.0, min(1.0, c)))

def circum(p):
    return np.linalg.solve(2*(p[1:]-p[0]), np.sum(p[1:]**2, axis=1)-np.sum(p[0]**2))

def switches_of(points, report_all=False):
    """For every hull edge (i,j) of the site set, the outward intersection of the
    perpendicular bisector with |x|=1 (the candidate switch).  Returns list of
    (i, j, x, radius) selecting, per hull edge, the vertex at distance <= 1 from origin
    that is Voronoi-nearest to both i and j."""
    hull = ConvexHull(points)
    out = []
    for (i, j) in hull.simplices:
        d = points[j]-points[i]; m = 0.5*(points[i]+points[j])
        nrm = np.array([d[1], -d[0]])/np.linalg.norm(d)
        s2 = 1.0 - m @ m
        if s2 < 0: continue
        for sgn in (+1, -1):
            t = -(m @ nrm) + sgn*math.sqrt((m @ nrm)**2 + s2)
            x = m + t*nrm
            di = np.linalg.norm(x-points[i])
            nearest = min(np.linalg.norm(x-q) for q in points)
            if di - nearest < 1e-9:
                out.append((int(i), int(j), x, di))
    return out

def cover_radius(points):
    """max over D of distance to nearest site = max over Voronoi vertices in D
    and over boundary transition points.  Exact for the finite Voronoi structure."""
    tri = Delaunay(points)
    best = 0.0
    for f in tri.simplices:
        v = circum(points[f]); r = np.linalg.norm(v-points[f[0]])
        if v @ v < 1.0: best = max(best, r)
    for i, j, x, rad in switches_of(points):
        best = max(best, rad)
    return best

def analyse(name, points, r=R, verbose=True):
    points = np.asarray(points, float)
    info = {'name': name}
    cr = cover_radius(points)
    info['cover_radius'] = round(cr, 12)
    info['is_cover_at_R'] = bool(cr <= R + 1e-12)
    rings = list(range(9))
    info['max_ring_norm'] = round(float(np.max(np.linalg.norm(points[rings], axis=1))), 12)
    info['max_hub_norm'] = round(float(np.max(np.linalg.norm(points[9:], axis=1))), 12)
    # order ring sites by angle
    order = sorted(rings, key=lambda i: math.atan2(points[i, 1], points[i, 0]))
    # switches between consecutive ring sites (2-ring Voronoi vertices on |x|=1)
    S = []
    for k in range(9):
        i = order[k]; j = order[(k+1) % 9]
        found = [t for t in switches_of(points) if {t[0], t[1]} == {i, j}]
        if not found:
            info['gap'] = f'no boundary switch for ring pair ({i},{j})'
            if verbose: print(json.dumps(info)); return info
        i2, j2, x, rad = found[0]
        S.append((i, j, x, rad))
    angS = [math.atan2(S[k][2][1], S[k][2][0]) % (2*math.pi) for k in range(9)]
    info['switch_radii'] = [round(t[3], 9) for t in S]
    info['max_switch_radius'] = round(max(t[3] for t in S), 12)
    # arc widths between consecutive switches in angular order
    idx = sorted(range(9), key=lambda k: angS[k])
    a = [angS[k] for k in idx]
    w = [(a[(m+1) % 9] - a[m]) % (2*math.pi) for m in range(9)]
    info['total_width'] = round(sum(w), 12)
    info['widths'] = [round(t, 9) for t in w]
    info['min_width'] = round(min(w), 9)
    # ownership: argmin site at each arc midpoint
    owner = []
    for m in range(9):
        mid = (a[m] + w[m]/2) % (2*math.pi)
        x = np.array([math.cos(mid), math.sin(mid)])
        d = np.array([np.linalg.norm(x-q) for q in points])
        owner.append(int(np.argmin(d)))
    info['owners'] = owner
    # is the arc between switch m and m+1 owned by the site that both switches share?
    ok = True
    for m in range(9):
        k = idx[m]; k2 = idx[(m+1) % 9]
        shared = set([S[k][0], S[k][1]]) & set([S[k2][0], S[k2][1]])
        if not shared or owner[m] not in shared: ok = False
    info['arc_owner_consistent'] = bool(ok)
    # closure residuals
    idxof = {k: m for m, k in enumerate(idx)}
    res = []
    for k in range(9):
        i, j, x, rad = S[k]
        prev = S[(k-1) % 9][2] if S[(k-1) % 9][1] == i else None
        nxt = S[(k+1) % 9][2] if S[(k+1) % 9][0] == j else None
        if prev is None or nxt is None:
            info['gap'] = 'switch chain broken'; break
        T = ang(prev - x, points[i] - x)
        L = ang(points[j] - x, nxt - x)
        apex = ang(points[i] - x, points[j] - x)
        m1 = idxof[k]; m2 = idxof[[kk for kk in range(9) if S[kk][0] == j][0]]
        wid = (w[m1] + w[m2])/2
        res.append(T + L + apex + wid - math.pi)
    info['closure'] = [round(t, 11) for t in res]
    info['closure_max_abs'] = round(max(abs(t) for t in res), 12)
    hullS = ConvexHull(np.array([S[k][2] for k in range(9)]))
    inside = all(np.max(hullS.equations[:, :2] @ q + hullS.equations[:, 2]) <= 1e-9 for q in points)
    info['all_sites_inside_switch_polygon'] = bool(inside)
    if verbose: print(json.dumps(info))
    return info

def load_saved():
    p = ROOT / 'n11' / 'upper' / 'certified_object.json'
    raw = json.loads(p.read_text(encoding='utf-8-sig'))
    a = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
    hubs = [0, 2]
    rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(a[i, 1], a[i, 0]))
    return a[rings + hubs]

if __name__ == '__main__':
    s = load_saved()
    print('saved candidate max |c| over all 11 =', round(float(np.max(np.linalg.norm(s, axis=1))), 12))
    print('=== saved certified upper candidate (9 rings ordered, then 2 hubs) ===')
    analyse('saved', s)
    print()
    print('=== random near-regular covers at r=R (Delaunay-random rings + hubs) ===')
    rng = np.random.default_rng(4242)
    nfail = 0; ntot = 0; worst = None
    for trial in range(60):
        th = np.sort(rng.uniform(0, 2*math.pi, 9))
        if np.min(np.diff(np.r_[th, th[0]+2*math.pi])) < 0.3: continue
        rr = 0.72 + rng.uniform(-0.05, 0.05, 9)
        c = np.c_[rr*np.cos(th), rr*np.sin(th)]
        hubs = rng.uniform(-0.32, 0.32, (2, 2))
        pts = np.vstack([c, hubs])
        inf = analyse('rand%d' % trial, pts, verbose=False)
        if not inf['is_cover_at_R']:
            print('rand%-3d not a cover (cover_radius %.6f)' % (trial, inf['cover_radius'])); continue
        ntot += 1
        m = inf['closure_max_abs']
        if worst is None or m > worst[1]: worst = (trial, m)
        if m > 1e-7:
            nfail += 1; print('FAIL', json.dumps(inf))
    print('covers tested:', ntot, ' closure failures (>1e-7):', nfail, ' worst:', worst)
