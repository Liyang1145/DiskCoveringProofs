"""Boundary ownership decomposition, exact:
- scipy Voronoi gives the 2-cells; intersect the far/near regions with |x|=1
- alternatively: exact half-plane clipping of each 2-cell against the unit disk.
Then: consecutive switches, arc widths, and the closure identity
T_i + L_(i+1) + 2 b_i + (w_i+w_(i+1))/2 = pi, with
 b_i = half of the angle at P_i between the two adjacent ring sites.
"""
import numpy as np, math, json
from pathlib import Path
from scipy.spatial import Voronoi, ConvexHull, HalfspaceIntersection, QhullError
ROOT = Path(__file__).resolve().parents[3]
R = 0.38

def clip_cell_unit_disk(points, i):
    hs = []
    for j in range(len(points)):
        if j == i: continue
        a = 2*(points[j]-points[i]); b = points[j] @ points[j] - points[i] @ points[i]
        hs.append(np.r_[a, -b])
    hs = np.array(hs)
    try:
        inter = HalfspaceIntersection(hs, 0.5*(points[i]+np.mean(points, axis=0)))
    except QhullError:
        return None
    poly = inter.intersections
    # clip polygon by |x|<=1
    out = []
    n = len(poly)
    for k in range(n):
        a = poly[k]; b = poly[(k+1) % n]
        ia = a @ a <= 1 + 1e-14; ib = b @ b <= 1 + 1e-14
        if ia: out.append(a)
        if ia != ib:
            d = b-a; A = d@d; B = 2*(a@d); C = a@a - 1
            disc = B*B-4*A*C
            if disc >= 0:
                s = math.sqrt(disc)
                for t in ((-B-s)/(2*A), (-B+s)/(2*A)):
                    if -1e-12 <= t <= 1+1e-12:
                        x = a+t*d
                        if abs(x@x-1) < 1e-9: out.append(x)
    if len(out) < 3: return None
    return np.array(out)

def cell_arc_angles(poly):
    """angles of the points of poly on |x|=1, sorted; the owned arc is the short one."""
    ang = sorted({round(math.atan2(x[1], x[0]) % (2*math.pi), 12) for x in poly if abs(x@x-1) < 1e-9})
    return ang

def load(path):
    raw = json.loads(Path(path).read_text(encoding='utf-8-sig'))
    a = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
    hubs = [0, 2]
    rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(a[i, 1], a[i, 0]))
    return a[rings+hubs]

c = load(ROOT/'n11'/'upper'/'certified_object.json')
print('site norms:', np.round(np.linalg.norm(c, axis=1), 9))
vor = Voronoi(c)
print('scipy: finite vertices at', np.round(vor.vertices, 6).tolist()[:6], '...')
print()
print('boundary arcs owned by each site (from clipped 2-cell):')
arcs = {}
for i in range(11):
    poly = clip_cell_unit_disk(c, i)
    if poly is None: continue
    ang = cell_arc_angles(poly)
    if len(ang) >= 2:
        arcs[i] = ang
        print('  site %2d  boundary angles %s' % (i, [round(t, 9) for t in ang]))
print()
print('sampling the boundary owner every 1 degree:')
owner = []
for k in range(360):
    th = k*math.pi/180
    x = np.array([math.cos(th), math.sin(th)])
    d = np.linalg.norm(c - x, axis=1)
    owner.append(int(np.argmin(d)))
runs = []
k = 0
while k < 360:
    j = k
    while j+1 < 360 and owner[j+1] == owner[k]: j += 1
    runs.append((k, j, owner[k])); k = j+1
if owner[0] == owner[-1] and len(runs) > 1:
    runs[0] = (runs[-1][0]-360, runs[0][1], runs[0][2]); runs.pop()
print(' owner runs (deg):', [(round(a*180/math.pi, 1), round(b*180/math.pi, 1), o) for a, b, o in runs])
print(' number of runs:', len(runs))
