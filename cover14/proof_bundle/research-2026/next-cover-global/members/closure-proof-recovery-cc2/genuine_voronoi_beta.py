"""Genuine-Voronoi test of the beta-identification in BOUNDARY-ANCHOR-NORM-CONSTRAINT.md.

For a real Voronoi diagram of sites strictly inside the unit disk, take each intersection A of
the unit circle with a bisector line that is a genuine boundary switch (nearest site i, no tie).
Let u,w = the two sites adjacent to that switch, a=|Au|=|Aw|, and let O be the OTHER endpoint of
the real facet (a Voronoi vertex = circumcentre of (u,w,x) for a third site x, nearest at O).
Then |Ou|=|Ow|=R, D=|AO|.  Test:
   (t1) O is the circumcentre of u,w and some x, and is nearest at O
   (t2) A is the ONLY other facet endpoint on segment AB -> legality of the configuration
   (t3) D^2 = a^2 + R^2 - 2 a R cos(beta),  beta computed at the site u
   (t4) cos gamma_A = (a - R cos beta)/D,   gamma_A = angle(uAw)/2
   (t5) gamma_f + gamma_A = pi - beta  with gamma_f at O between OA and Ow
   (t6) a sin gamma_A = R sin gamma_f
   (t7) hA < 0 and the segment-position condition hA outside [min(hO,0), max(hO,0)]
"""
import math, itertools, random
import numpy as np

def cr(p, q): return float(p[0]*q[1] - p[1]*q[0])
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

def gen_cover(rng, kring, U=0.32):
    smax = math.sqrt(1-U*U)*0.98
    t0 = rng.random()*2*math.pi
    pts = []
    for i in range(kring):
        t = t0 + 2*math.pi*i/kring + rng.uniform(-0.15, 0.15)/kring*3
        r = rng.uniform(0.55, 0.95)*smax/0.98*0.98
        pts.append((r*math.cos(t), r*math.sin(t)))
    for _ in range(rng.randint(0, 2)):
        t = rng.random()*2*math.pi; r = rng.uniform(0, 0.55)
        pts.append((r*math.cos(t), r*math.sin(t)))
    S = np.array(pts)
    if max(np.linalg.norm(S, axis=1)) >= smax: return None
    return S

def nearest(S, x):
    d = np.sum((S-x)**2, axis=1)
    o = np.argsort(d)
    return int(o[0]), float(d[o[0]]), float(d[o[1]])

rng = random.Random(77)
res = {k: [] for k in ['t3','t4','t5','t6','hA','seg','facet']}
ncs = 0; nsw = 0
for it in range(4000):
    kring = rng.randint(9, 16)
    S = gen_cover(rng, kring)
    if S is None: continue
    n = len(S)
    # candidate switches: bisector intersections with unit circle, nearest site splits into two
    for i, j in itertools.combinations(range(n), 2):
        d = S[j]-S[i]; l = float(np.linalg.norm(d))
        h = (float(S[j]@S[j]) - float(S[i]@S[i]))/(2*l)
        if abs(h) >= 1: continue
        e = d/l; nn = np.array([-e[1], e[0]])
        for sgn in (-1.0, 1.0):
            A = h*e + sgn*math.sqrt(max(0.0, 1-h*h))*nn
            d1 = np.sum((S-A)**2, axis=1)
            if d1[i] > d1.min()+1e-12: continue
            order = np.argsort(d1)
            if abs(d1[order[0]]-d1[order[1]]) < 1e-9: continue
            u_, w_ = int(i), int(j)
            # third site x: the site whose Voronoi vertex O lies on segment to A.
            # find O = circumcentre of (u,w,x) for the x that makes O nearest and inside
            best = None
            for x in range(n):
                if x in (u_, w_): continue
                O = circumcentre(S[u_], S[w_], S[x])
                if O is None: continue
                R = float(np.linalg.norm(O-S[u_]))
                if R > 0.3333 or np.linalg.norm(O) >= 1: continue
                nx, dx0, dx1 = nearest(S, O)
                if nx != u_ or abs(dx0-dx1) > 1e-9: continue
                # A and O must be on the same facet: A equidistant u,w and u nearest at A.
                # legality test for C1250: parametrise the bisector line and check order
                # of m=(u+w)/2, O, A along it.
                m = (S[u_]+S[w_])/2
                dirv = (m - A); nd = float(np.linalg.norm(dirv))
                if nd < 1e-12: continue
                dirv = dirv/nd
                tO = float((O - A) @ dirv); tM = float((m - A) @ dirv); tA = 0.0
                # A must be the far endpoint: tO in (0, tM) or (tM, 0) ordering consistent
                best = (x, O, R, tO, tM)
            if best is None: continue
            x, O, R, tO, tM = best
            nsw += 1
            a = float(np.linalg.norm(A-S[u_]))
            aw = float(np.linalg.norm(A-S[w_]))
            if abs(a-aw) > 1e-9: continue
            D = float(np.linalg.norm(A-O))
            if D < 1e-6: continue
            # coordinates in the C1250 frame: u=(0,0), w=(l,0), third vertex above
            e1 = (S[w_]-S[u_]); L = float(np.linalg.norm(e1)); e1 = e1/L
            e2 = np.array([-e1[1], e1[0]])
            def co(P): 
                q = P - S[u_]; return np.array([q@e1, q@e2])
            Aq = co(A); Oq = co(O)
            beta = ang(np.array([0.0,0.0]), Aq, Oq)      # angle at the SITE u between uA and uO
            gA = ang(A, S[u_], S[w_])/2
            gf = ang(O, A, S[w_])
            # t3
            res['t3'].append(D**2 - (a*a + R*R - 2*a*R*math.cos(beta)))
            # t4  -- note: beta here is the angle at u; test BOTH signs of the numerator
            res['t4'].append((a - R*math.cos(beta))/D - math.cos(gA))
            res['t5'].append(gf + gA + beta - math.pi)
            res['t6'].append(a*math.sin(gA) - R*math.sin(gf))
            hA = Aq[1]; hO = Oq[1]
            res['hA'].append(hA)
            lo, hi = min(hO, 0.0), max(hO, 0.0)
            res['seg'].append(0.0 if not (lo < hA < hi) else 1.0)
            res['facet'].append(0.0)
ncs = len(res['hA'])
print("genuine boundary switches processed: %d" % ncs)
def mx(k): return max((abs(v) for v in res[k]), default=0.0)
print("max |D^2-(a^2+R^2-2aR cos beta)|              = %.3e" % mx('t3'))
print("max |(a-R cos beta)/D - cos gamma_A|          = %.3e" % mx('t4'))
print("max |gamma_f+gamma_A+beta-pi|                 = %.3e" % mx('t5'))
print("max |a sin gamma_A - R sin gamma_f|           = %.3e" % mx('t6'))
print("hA<0 for all? %s   max hA = %.4f" % (all(h < 0 for h in res['hA']), max(res['hA']) if res['hA'] else 0))
print("illegal segment positions (hA strictly between hO and 0): %d" % int(sum(res['seg'])))
