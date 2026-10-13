"""Hub-free reformulation, calibrated on the certified ring.

D = unit disk.  9 "ring" disks B(a_j,r) of radius r must
  (i)  cover bd(D)            [hubs cannot reach bd(D): |h|+r < 1]
  (ii) leave a hole H = D \\ U B(a_j,r) that two further disks of the SAME radius r
       can cover.
Conditions (i)+(ii) are necessary and sufficient for an 11-disk cover at radius r
(the two extra disks ARE the hubs; no other role for them).

Hole closure extreme points: intersections of pairs of ring circles that lie
outside all rings, plus intersections with bd(D).
Then:  T1(H) = min enclosing radius (1 disk),  T2(H) = min radius for 2 equal disks
(computed by the perpendicular-bisector sweep: the optimal 2-centre split of a
finite point set is a line split).
"""
import numpy as np, io, json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from itertools import combinations

d = json.load(io.open('n11/upper/certified_object.json', encoding='utf-8'))
C = np.array([[int(a)/1e17, int(b)/1e17] for a, b in d['centers_scaled_1e17']])
rho = np.hypot(C[:, 0], C[:, 1])
R9 = C[rho >= 0.62]
r = 0.3799838531198387090          # the certified radius of that object

def circle_intersections(a, b, r):
    dvec = b - a; L = np.hypot(*dvec)
    if L == 0 or L > 2*r:
        return []
    u = dvec/L; n = np.array([-u[1], u[0]])
    h = np.sqrt(max(0.0, r*r - (L/2)**2))
    m = 0.5*(a + b)
    return [m + h*n, m - h*n]

cands = []
for i, j in combinations(range(len(R9)), 2):
    for p in circle_intersections(R9[i], R9[j], r):
        if np.hypot(*p) <= 1 + 1e-12:
            cands.append(p)
cands = np.array(cands)
# keep only points outside (or on) every ring  -> points of cl(H)
keep = np.array([np.min(np.linalg.norm(R9 - p, axis=1)) >= r - 1e-9 for p in cands])
H = cands[keep]
print("ring circles pair intersections:", len(cands), " in cl(H):", len(H))
print("  |p| range [%.6f, %.6f]" % (np.hypot(H[:,0], H[:,1]).min(), np.hypot(H[:,0], H[:,1]).max()))

# --- 1-centre radius of H (exact brute force over pairs/triples)
def meb(pts):
    n = len(pts); best = (None, 1e9)
    for i in range(n):
        c = pts[i]; rad = 0.0
        if all(np.linalg.norm(p-c) <= rad+1e-12 for p in pts): best = min(best, (c, rad), key=lambda t: t[1])
    for i, j in combinations(range(n), 2):
        c = 0.5*(pts[i]+pts[j]); rad = np.linalg.norm(pts[i]-c)
        if all(np.linalg.norm(p-c) <= rad+1e-12 for p in pts): best = min(best, (c, rad), key=lambda t: t[1])
    for i, j, k in combinations(range(n), 3):
        A, B, Cc = pts[i], pts[j], pts[k]
        dd = 2*(A[0]*(B[1]-Cc[1]) + B[0]*(Cc[1]-A[1]) + Cc[0]*(A[1]-B[1]))
        if abs(dd) < 1e-15: continue
        ux = ((A@A)*(B[1]-Cc[1]) + (B@B)*(Cc[1]-A[1]) + (Cc@Cc)*(A[1]-B[1]))/dd
        uy = ((A@A)*(Cc[0]-B[0]) + (B@B)*(A[0]-Cc[0]) + (Cc@Cc)*(B[0]-A[0]))/dd
        c = np.array([ux, uy]); rad = max(np.linalg.norm(p-c) for p in pts)
        if all(np.linalg.norm(p-c) <= rad+1e-12 for p in pts): best = min(best, (c, rad), key=lambda t: t[1])
    return best

c1, T1 = meb(H)
print("one-disc radius T1(H) = %.10f   (centre %s)" % (T1, np.round(c1, 6)))

# --- 2-equal-disc radius of H: sweep the separating line
def two_centre_radius(pts, ndir=1440):
    best = 1e9; info = None
    for t in np.linspace(0, np.pi, ndir, endpoint=False):
        u = np.array([np.cos(t), np.sin(t)])
        proj = pts @ u
        order = np.argsort(proj); P = pts[order]; pr = proj[order]
        # candidate splits at midpoints between consecutive projections
        cuts = np.unique(np.concatenate([[0], np.where(np.diff(pr) > 1e-12)[0]+1, [len(P)]]))
        for k in cuts:
            if k == 0 or k == len(P): continue
            _, r1 = meb(P[:k]); _, r2 = meb(P[k:])
            m = max(r1, r2)
            if m < best: best = m; info = (t, k, r1, r2)
    return best, info

T2, info = two_centre_radius(H)
print("two-disc radius T2(H) = %.10f  (dir=%.4f split=%d r1=%.8f r2=%.8f)" % ((T2,)+info))
print("compare r = %.10f :  T2 <= r ? %s   slack r - T2 = %.3e" % (r, T2 <= r, r - T2))

# --- arc side: maximum arc half width  = asin r   (attained at |a| = sqrt(1-r^2))
print("\narc half-width bound: asin(r) = %.10f ; 9 arcs total <= %.6f ; 2pi = %.6f" %
      (np.arcsin(r), 18*np.arcsin(r), 2*np.pi))
print("   => arc-capacity slack = %.6f" % (18*np.arcsin(r) - 2*np.pi))
