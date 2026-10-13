"""CORRECTED geometry test.  Signed angles via cross/dot, correct switch table.

Facts to establish numerically on the saved candidate (exact coordinates):
 (A) every site is strictly inside the convex hull K of the 9 switches
     (oriented half-plane test with the INTERIOR normal),
 (B) the arc widths from the switch table (they were right),  sum = 2 pi,
 (C) signed-consistency of the ray order at each switch:
       cross(P_{k-1}-P_k, c_k-P_k) and cross(P_{k+1}-P_k, c_k-P_k) have the SAME sign
       (c_k's ray lies strictly inside the interior angle of K at P_k),
 (D) the closure identity with T,L as *interior* fan angles:
       T_k + L_(k+1) + apex_k + (w_k + w_(k+1))/2 = pi,  apex_k = signed angle
       between the two ring-site rays at P_k measured INSIDE K.
"""
import numpy as np, math, json
from pathlib import Path
from scipy.spatial import ConvexHull
ROOT = Path(__file__).resolve().parents[3]

def cross(u, v): return float(u[0]*v[1]-u[1]*v[0])
def dot(u, v):  return float(u @ v)
def sang(u, v): return math.atan2(cross(u, v), dot(u, v))       # signed in (-pi,pi]
def aabs(u, v): return math.atan2(abs(cross(u, v)), dot(u, v))  # unsigned in [0,pi]

def load(path):
    raw = json.loads(Path(path).read_text(encoding='utf-8-sig'))
    a = np.array([[int(x)/1e17 for x in row] for row in raw['centers_scaled_1e17']])
    hubs = [0, 2]
    rings = sorted([i for i in range(11) if i not in hubs], key=lambda i: math.atan2(a[i, 1], a[i, 0]))
    return a[rings+hubs]

def switches(c, ringpairs):
    """switch for each ordered ring pair = |x|=1 point nearest to both."""
    out = {}
    for (i, j) in ringpairs:
        m = 0.5*(c[i]+c[j]); d = c[j]-c[i]
        n = np.array([d[1], -d[0]])/np.linalg.norm(d)
        t0 = -(m @ n); s2 = 1 - m @ m
        if s2 < 0: return None
        got = []
        for sgn in (+1, -1):
            x = m + (t0+sgn*math.sqrt(t0*t0+s2))*n
            di = np.linalg.norm(x-c[i]); dj = np.linalg.norm(x-c[j])
            if abs(di-dj) > 1e-9: continue
            if di - min(np.linalg.norm(x-q) for q in c) > 1e-9: continue
            got.append(x)
        if len(got) != 1: return None
        out[(i, j)] = got[0]
    return out

def audit(c, name, verbose=True):
    c = np.asarray(c, float)
    pairs = [(k, (k+1) % 9) for k in range(9)]
    S = switches(c, pairs)
    if S is None: return None
    # cyclic order and widths
    order = sorted(range(9), key=lambda k: math.atan2(S[(k, (k+1) % 9)][1], S[(k, (k+1) % 9)][0]) % (2*math.pi))
    th = [math.atan2(S[(k, (k+1) % 9)][1], S[(k, (k+1) % 9)][0]) % (2*math.pi) for k in order]
    w = [(th[(m+1) % 9]-th[m]) % (2*math.pi) for m in range(9)]
    wof = {order[m]: w[m] for m in range(9)}
    P = [S[(k, (k+1) % 9)] for k in range(9)]
    # (A) containment with interior normal
    hull = ConvexHull(np.array(P))
    cen = np.array(P).mean(axis=0)
    inside = True; worst = -1e9
    for x in c:
        for (a, b) in hull.simplices:
            q1, q2 = np.array(P)[a], np.array(P)[b]
            n = np.array([-(q2-q1)[1], (q2-q1)[0]])
            if dot(cen-q1, n) < 0: n = -n
            val = dot(x-q1, n)
            worst = max(worst, val)
            if val > 1e-12: inside = False
    # (C) ray order and (D) closure
    rc = []; inw = 0
    for k in range(9):
        Pk = P[k]; Pm = P[(k-1) % 9]; Pp = P[(k+1) % 9]
        u = Pm - Pk; v = Pp - Pk; x = c[k] - Pk
        c1 = cross(u, x); c2 = cross(v, x)
        if c1*c2 > 0: inw += 1
        # interior angles at Pk
        T = aabs(u, x); L = aabs(x, v)
        apex = aabs(c[k]-Pk, c[(k+1) % 9]-Pk)
        rc.append(T + L + apex + (wof[(k-1) % 9]+wof[k])/2 - math.pi)
    info = dict(name=name, total_width=sum(w), min_width=min(w),
                all_sites_inside_K=inside, max_outward_slack=worst,
                ray_inside_count=inw, closure_max=max(abs(t) for t in rc))
    if verbose: print(json.dumps(info))
    return info, P, S, wof

if __name__ == '__main__':
    c = load(ROOT/'n11'/'upper'/'certified_object.json')
    audit(c, 'saved candidate')
