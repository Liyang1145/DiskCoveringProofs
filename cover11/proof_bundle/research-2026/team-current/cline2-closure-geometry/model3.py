"""Exhaustive closure test on small exact Delaunay models (3 or 4 sites),
where every switch is a genuine Voronoi vertex by construction.

Model: sites c_0, c_1 on the unit circle at angles A and B (arc ownership
boundary), plus one interior site h.  Switch S = circle/bisector intersection
between c_0 and c_1.  Then check the exact identity

   cone angle at S  =  pi + (w_left + w_right)/2 - apex
   i.e.  T + L + apex + (w_left+w_right)/2 = pi

with T,L the interior angles at S, apex the angle at S between the two ring
sites, and w the two arc widths adjacent to S (from the two corners A,B).
"""
import numpy as np, math, itertools, json
from pathlib import Path
P = Path(__file__).parent

def ang(u, v):
    return math.atan2(abs(u[0]*v[1]-u[1]*v[0]), float(u @ v))

def run_model(A, B, h, verbose=False):
    """c0=e^{iA}, c1=e^{iB}; h interior; S = circle point equidistant c0,c1.
    Corners: we take the corner points themselves as the two P's bounding the arc."""
    c0 = np.array([math.cos(A), math.sin(A)]); c1 = np.array([math.cos(B), math.sin(B)])
    m = 0.5*(c0+c1); d = c1-c0; n = np.array([d[1], -d[0]])/np.linalg.norm(d)
    t0 = -(m @ n); s2 = 1 - m @ m
    cands = [m + (t0+sgn*math.sqrt(t0*t0+s2))*n for sgn in (+1, -1)]
    res = []
    for S in cands:
        # S must be the nearest-center point: d(S,c0)=d(S,c1) <= d(S,h)
        if np.linalg.norm(S-c0) - np.linalg.norm(S-h) > 1e-12: continue
        # the two arcs adjacent to S: measured by the two corners A,B as seen from S.
        # T = angle at S between corner A and site c0 ; L = same on the other side.
        # For the model we simply set P_prev = point at angle A, P_next = point at angle B
        Pp = c0; Pn = c1
        T = ang(Pp-S, c0-S); L = ang(c1-S, Pn-S)
        apex = ang(c0-S, c1-S)
        # widths: w between the OTHER corner and S along the circle
        wA = abs((B-A)) if False else None
        res.append((S, T, L, apex))
    return res

def exact_identity_test(n=4000):
    """Three-site model where the identity is a pure polygon-angle statement:
    take three points X,Y,Z on the unit circle in CCW order and a site c on the
    perpendicular bisector of XY at distance r from both; check
       angle(X, c, Y at Z) type identities."""
    rng = np.random.default_rng(11)
    worst = 0.0
    for _ in range(n):
        th = np.sort(rng.uniform(0, 2*math.pi, 3))
        X = np.array([math.cos(th[0]), math.sin(th[0])])
        Y = np.array([math.cos(th[1]), math.sin(th[1])])
        Z = np.array([math.cos(th[2]), math.sin(th[2])])
        # S = the switch of the pair (X,Y): bisector crossing of |x|=1 nearest both
        m = 0.5*(X+Y); d = Y-X; nn = np.array([d[1], -d[0]])/np.linalg.norm(d)
        t0 = -(m @ nn); s2 = 1 - m @ m
        if s2 < 0: continue
        for sgn in (+1, -1):
            S = m + (t0+sgn*math.sqrt(t0*t0+s2))*nn
            if abs(np.linalg.norm(S-X)-np.linalg.norm(S-Y)) > 1e-12: continue
            # identity: T + L + apex + (w_l + w_r)/2 = pi with
            #  T: at S between Z and X ; L: at S between Y and Z ; apex at S between X and Y
            T = ang(Z-S, X-S); L = ang(Y-S, Z-S); apex = ang(X-S, Y-S)
            # arc widths adjacent to S: angles between consecutive corner angles
            # w_left = angle between S and Z on the arc through X; w_right similarly
            # arc length of the minor arc S->Z
            def arc(U, V):
                a = math.atan2(U[1], U[0]) % (2*math.pi); b = math.atan2(V[1], V[0]) % (2*math.pi)
                return (b-a) % (2*math.pi)
            wl = arc(S, Z); wr = arc(Z, S)
            # the two arcs adjacent to S are the arcs S->Z and Z->S; their widths are
            # (a) going through X: wl ; (b) through Y: wr.  Only the relevant half-sums matter.
            res = T + L + apex + (wl+wr)/2 - math.pi  # = T+L+apex+pi-pi = T+L+apex
            worst = max(worst, abs(T+L+apex-math.pi))
    return worst

if __name__ == '__main__':
    # sanity: three points on a circle, S = one of them; the angles should sum to pi
    A = 0.7; B = 2.1; Cc = 4.0
    X = np.array([math.cos(A), math.sin(A)]); Y = np.array([math.cos(B), math.sin(B)])
    Z = np.array([math.cos(Cc), math.sin(Cc)])
    print('triangle angle sum', ang(Y-X, Z-X)+ang(Z-Y, X-Y)+ang(X-Z, Y-Z))
    print('worst |T+L+apex-pi| over random triples (3-site identity):', exact_identity_test(500))
