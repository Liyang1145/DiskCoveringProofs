"""Decisive genuine-Voronoi probe: 11 ring sites at radius d (11-gon, R=2pi/11) + optional
interior sites, all strictly inside the unit disk, giving a legal cover of the disk boundary.
For every genuine boundary switch A we identify the two adjacent owners u,w and the second
facet endpoint O (the Voronoi vertex of (u,w,x) whose cell contains A), then report the exact
readings of every premise the two audited arguments use.
"""
import math, itertools
import numpy as np

def cr(p, q): return float(p[0]*q[1]-p[1]*q[0])
def ang(P, Q, Z):
    p = np.array(Q, float)-np.array(P, float); q = np.array(Z, float)-np.array(P, float)
    return math.atan2(abs(cr(p, q)), float(p@q))
def circumcentre(P, Q, R):
    ax, ay = P; bx, by = Q; cx, cy = R
    d = 2*(ax*(by-cy)+bx*(cy-ay)+cx*(ay-by))
    if abs(d) < 1e-14: return None
    ux = ((ax*ax+ay*ay)*(by-cy)+(bx*bx+by*by)*(cy-ay)+(cx*cx+cy*cy)*(ay-by))/d
    uy = ((ax*ax+ay*ay)*(cx-bx)+(bx*bx+by*by)*(ax-cx)+(cx*cx+cy*cy)*(bx-ax))/d
    return np.array([ux, uy])

def run(kring=11, d=0.93, inner=None, U=1/3, label=""):
    U = float(U)
    pts = []
    for i in range(kring):
        t = 2*math.pi*i/kring + 0.137
        pts.append((d*math.cos(t), d*math.sin(t)))
    if inner:
        pts.extend(inner)
    S = np.array(pts); n = len(S)
    smax = math.sqrt(1-U*U)
    print("=" * 100)
    print("%s  kring=%d d=%.3f  n=%d  max|site|=%.4f  s=sqrt(1-U^2)=%.4f  OK=%s"
          % (label, kring, d, n, max(np.linalg.norm(S, axis=1)), smax, max(np.linalg.norm(S, axis=1)) < smax))
    # switches: bisector crossings of S1 where two sites are the nearest pair
    sw = []
    for i, j in itertools.combinations(range(n), 2):
        dl = S[j]-S[i]; l = float(np.linalg.norm(dl))
        h = (float(S[j]@S[j])-float(S[i]@S[i]))/(2*l)
        if abs(h) >= 1: continue
        e = dl/l; nn = np.array([-e[1], e[0]])
        for sgn in (-1.0, 1.0):
            A = h*e + sgn*math.sqrt(max(0.0, 1-h*h))*nn
            d1 = np.sum((S-A)**2, axis=1); o = np.argsort(d1)
            if abs(d1[o[0]]-d1[o[1]]) > 1e-9: continue
            if {int(o[0]), int(o[1])} != {i, j}: continue
            sw.append((math.atan2(A[1], A[0]) % (2*math.pi), A, int(o[0]), int(o[1])))
    sw.sort(key=lambda z: z[0])
    ded = []
    for t, A, i, j in sw:
        if ded and abs((t-ded[-1][0]+math.pi) % (2*math.pi)-math.pi) < 1e-9: continue
        ded.append((t, A, i, j))
    sw = ded
    print("genuine boundary switches: %d" % len(sw))
    if not sw: return
    q = len(sw)
    # owners of arcs
    own = []
    for idx in range(q):
        t, A, i, j = sw[idx]; tp, Ap, ip, jp = sw[(idx+1) % q]
        thp = (tp-t) % (2*math.pi)
        mid = (t+thp/2) % (2*math.pi)
        p = np.array([math.cos(mid), math.sin(mid)])
        w = int(np.argmin(np.sum((S-p)**2, axis=1)))
        own.append(w)
    rho = max(math.sqrt(float(np.min(np.sum((S-np.array([math.cos(k*2*math.pi/4000), math.sin(k*2*math.pi/4000)]))**2, axis=1))))
              for k in range(4000))
    print("covering radius rho = %.6f   <= U=%.4f ? %s" % (rho, U, rho <= U+1e-9))
    print("%4s %8s %8s %8s %8s %9s %9s %9s %9s %7s %7s" %
          ("idx","theta_u","theta_v","a","hA","hO","D","beta","gamma_A","cos>=k","legal"))
    worst = dict(cone=9, beta=0, law=0, cyc=0, seg=0)
    for idx in range(q):
        t, A, i, j = sw[idx]
        tp, Ap, ip, jp = sw[(idx+1) % q]
        thm = (t-sw[(idx-1) % q][0]) % (2*math.pi); thp = (tp-t) % (2*math.pi)
        u = own[(idx-1) % q]; v = own[idx]
        if u == v or {u, v} != {i, j}: continue
        # second facet endpoint O: circumcentre of (u,v,x) nearest-consistent and inside
        best = None
        for x in range(n):
            if x in (u, v): continue
            O = circumcentre(S[u], S[v], S[x])
            if O is None: continue
            R = float(np.linalg.norm(O-S[u]))
            if R > U or np.linalg.norm(O) >= 1: continue
            dd = np.sum((S-O)**2, axis=1); oo = np.argsort(dd)
            if oo[0] != u or abs(dd[oo[0]]-dd[oo[1]]) > 1e-9: continue
            best = (O, R, x)
        if best is None:
            print("%4d  no legal second endpoint (u=%d v=%d)" % (idx, u, v)); continue
        O, R, x = best
        e1 = S[v]-S[u]; L = float(np.linalg.norm(e1)); e1 = e1/L
        e2 = np.array([-e1[1], e1[0]])
        Aq = np.array([ (A-S[u])@e1, (A-S[u])@e2 ])
        Oq = np.array([ (O-S[u])@e1, (O-S[u])@e2 ])
        a = float(np.linalg.norm(A-S[u])); D = float(np.linalg.norm(A-O))
        beta = ang(np.array([0.0, 0.0]), Aq, Oq)
        gA = ang(A, S[u], S[v])/2
        gf = ang(O, A, S[v])
        ka = (a*a+U*U)/(2*a)
        legal = 0.0 if not (min(Oq[1], 0.0) < Aq[1] < max(Oq[1], 0.0)) else 1.0
        worst['cone'] = min(worst['cone'], math.cos(gA)-ka)
        worst['beta'] = max(worst['beta'], abs((a-R*math.cos(beta))/D - math.cos(gA)))
        worst['law'] = max(worst['law'], abs(D*D-(a*a+R*R-2*a*R*math.cos(beta))))
        worst['cyc'] = max(worst['cyc'], abs(gf+gA+beta-math.pi))
        worst['seg'] += legal
        print("%4d %8.4f %8.4f %8.4f %8.4f %8.4f %9.5f %9.5f %9.5f %7.2f %7.0f" %
              (idx, thm, thp, a, Aq[1], Oq[1], D, beta, gA, math.cos(gA)-ka, legal))
    print("min(cos gamma_A - k(a)) = %.3e ; max beta-formula residual = %.2e ; max law residual = %.2e ; max cyclicity residual = %.2e ; illegal-segment count = %d"
          % (worst['cone'], worst['beta'], worst['law'], worst['cyc'], worst['seg']))

run(11, 0.93, None, label="symmetric 11-ring only")
run(11, 0.93, [(0.0, 0.0), (0.25, -0.18)], label="11-ring + 2 interior")
run(12, 0.90, [(0.1, 0.2)], label="12-ring + 1 interior")
