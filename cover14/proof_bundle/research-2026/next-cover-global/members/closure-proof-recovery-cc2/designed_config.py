"""Designed genuine Voronoi configuration (11 boundary owners + 3 interior sites, 14 total),
all sites strictly inside the unit disk, with the real-face centres placed explicitly and
NEAREST-CHECKED.  Purpose: obtain legal boundary switches for the exact premises of
BOUNDARY-CYCLICITY-PROOF.md and BOUNDARY-ANCHOR-NORM-CONSTRAINT.md and read off the residuals.

Construction: sites u_0..u_10 on a circle of radius r_s (< sqrt(1-U^2)), interior sites
x,y,z near the centre.  Voronoi vertices are circumcentres of Delaunay triangles; we verify
"nearest" at every vertex and print, per boundary switch A:
   theta_u, theta_v, a, hA, hO, D, beta(at site u), gamma_A, cos gamma_A - k(a),
   (a-R cos beta)/D - cos gamma_A, gamma_f+gamma_A+beta-pi, segment legality.
"""
import math
import numpy as np

def cr(p, q): return float(p[0]*q[1]-p[1]*q[0])
def ang(P, Q, Z):
    p = np.array(Q, float)-np.array(P, float); q = np.array(Z, float)-np.array(P, float)
    return math.atan2(abs(cr(p, q)), float(p@q))
def cc(P, Q, R):
    ax, ay = P; bx, by = Q; cx, cy = R
    d = 2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
    if abs(d) < 1e-14: return None
    ux = ((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/d
    uy = ((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/d
    return np.array([ux, uy])

U = 1/3.0
smax = math.sqrt(1-U*U)
k = 11
rs = 0.94
S = [np.array([rs*math.cos(2*math.pi*i/k+0.211), rs*math.sin(2*math.pi*i/k+0.211)]) for i in range(k)]
S += [np.array([0.02, 0.01]), np.array([0.30, -0.22]), np.array([-0.26, 0.19])]
S = np.array(S); n = len(S)
print("n=%d  max|site|=%.4f < s=%.4f  OK=%s" % (n, max(np.linalg.norm(S, axis=1)), smax,
                                                max(np.linalg.norm(S, axis=1)) < smax))

def nearest2(P):
    d = np.sum((S-P)**2, axis=1); o = np.argsort(d)
    return int(o[0]), int(o[1]), float(d[o[1]]-d[o[0]])

# Delaunay triangles (combinatorics of a fan over the ring + interior): u_i u_{i+1} with each of
# the three interior sites, plus the central triangle.  Verify each has an empty circumcircle.
tris = []
for i in range(k):
    for x in (11, 12, 13):
        tris.append((i, (i+1) % k, x))
tris.append((11, 12, 13))
verts = []
for (a, b, c) in tris:
    O = cc(S[a], S[b], S[c])
    if O is None: continue
    R = float(np.linalg.norm(O-S[a]))
    dd = np.sqrt(np.sum((S-O)**2, axis=1))
    nm = int(np.argmin(dd))
    if nm in (a, b, c) and R < U:
        verts.append((O, R, (a, b, c), dd[np.argsort(dd)[1]]-dd[nm]))
print("Voronoi vertices with R<U and nearest-consistent: %d / %d triangles" % (len(verts), len(tris)))

# boundary switches: crossings of the unit circle with bisector lines, nearest pair must be the pair
sw = []
for i in range(n):
    for j in range(i+1, n):
        dl = S[j]-S[i]; l = float(np.linalg.norm(dl))
        h = (float(S[j]@S[j]) - float(S[i]@S[i]))/(2*l)
        if abs(h) >= 1: continue
        e = dl/l; nn = np.array([-e[1], e[0]])
        for sgn in (-1.0, 1.0):
            A = h*e + sgn*math.sqrt(max(0.0, 1-h*h))*nn
            o0, o1, gap = nearest2(A)
            if {o0, o1} != {i, j} or gap < 1e-12: continue
            sw.append((math.atan2(A[1], A[0]) % (2*math.pi), A, o0, o1))
sw.sort(key=lambda z: z[0])
ded = []
for t, A, i, j in sw:
    if ded and abs((t-ded[-1][0]+math.pi) % (2*math.pi)-math.pi) < 1e-9: continue
    ded.append((t, A, i, j))
sw = ded; q = len(sw)
print("genuine boundary switches: %d" % q)
# owner of each arc
own = []
for idx in range(q):
    t, A, i, j = sw[idx]; tp = sw[(idx+1) % q][0]
    thp = (tp-t) % (2*math.pi); mid = (t+thp/2) % (2*math.pi)
    p = np.array([math.cos(mid), math.sin(mid)])
    own.append(int(np.argmin(np.sum((S-p)**2, axis=1))))
print("owners:", own)
print()
print("%4s %7s %7s %7s %8s %8s %8s %8s %8s %10s %10s %10s %6s" %
      ("idx","th_u","th_v","a","hA","hO","D","beta","gamma_A","cos-k(a)","beta-res","cyc-res","legal"))
w = dict(cone=9.0, beta=0.0, law=0.0, cyc=0.0, seg=0)
count = 0
for idx in range(q):
    t, A, i, j = sw[idx]
    tp = sw[(idx+1) % q][0]
    thm = (t-sw[(idx-1) % q][0]) % (2*math.pi); thp = (tp-t) % (2*math.pi)
    u = own[(idx-1) % q]; v = own[idx]
    if u == v or {u, v} != {i, j}: continue
    # find the Voronoi vertex O of a triangle containing both u and v, nearest-consistent
    cand = [V for V in verts if u in V[2] and v in V[2]]
    if not cand:
        print("%4d  no shared Voronoi vertex (u=%d v=%d) -- facet may be a boundary-hugging ray" % (idx, u, v))
        continue
    O, R, tri, margin = cand[0]
    e1 = S[v]-S[u]; L = float(np.linalg.norm(e1)); e1 = e1/L; e2 = np.array([-e1[1], e1[0]])
    Aq = np.array([(A-S[u])@e1, (A-S[u])@e2]); Oq = np.array([(O-S[u])@e1, (O-S[u])@e2])
    a = float(np.linalg.norm(A-S[u])); D = float(np.linalg.norm(A-O))
    beta = ang(np.array([0., 0.]), Aq, Oq)
    gA = ang(A, S[u], S[v])/2; gf = ang(O, A, S[v])
    ka = (a*a+U*U)/(2*a)
    legal = 0.0 if not (min(Oq[1], 0.0) < Aq[1] < max(Oq[1], 0.0)) else 1.0
    w['cone'] = min(w['cone'], math.cos(gA)-ka)
    w['beta'] = max(w['beta'], abs((a-R*math.cos(beta))/D - math.cos(gA)))
    w['law'] = max(w['law'], abs(D*D-(a*a+R*R-2*a*R*math.cos(beta))))
    w['cyc'] = max(w['cyc'], abs(gf+gA+beta-math.pi))
    w['seg'] += legal; count += 1
    print("%4d %7.4f %7.4f %7.4f %8.4f %8.4f %8.5f %8.5f %8.5f %10.2e %10.2e %10.2e %6.0f" %
          (idx, thm, thp, a, Aq[1], Oq[1], D, beta, gA, math.cos(gA)-ka,
           abs((a-R*math.cos(beta))/D-math.cos(gA)), abs(gf+gA+beta-math.pi), legal))
print()
print("switches with a shared legal Voronoi vertex: %d" % count)
print("min(cos gamma_A - k(a)) = %.4e   (must be >= 0)" % w['cone'])
print("max |beta formula residual| = %.3e ; max |law residual| = %.3e ; max |cyclicity residual| = %.3e"
      % (w['beta'], w['law'], w['cyc']))
print("illegal segment positions: %d" % int(w['seg']))
rho = max(math.sqrt(float(np.min(np.sum((S-np.array([math.cos(kk*2*math.pi/20000), math.sin(kk*2*math.pi/20000)]))**2, axis=1))))
          for kk in range(20000))
print("covering radius rho = %.6f <= U? %s" % (rho, rho <= U+1e-9))
print("owned arcs <= 2 asin rho? max arc given above; 2 asin rho = %.4f" % (2*math.asin(min(1, rho))))
