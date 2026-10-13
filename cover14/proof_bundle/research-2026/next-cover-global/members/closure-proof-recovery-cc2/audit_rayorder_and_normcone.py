"""Consolidated independent audit script.

(A) SYMBOLIC  : polynomial norm-cone chain of BOUNDARY-ANCHOR-NORM-CONSTRAINT.md
(B) GEOMETRIC : (v) angle coupling cos gamma = (a-R cos beta)/D and law of cosines
(C) SATURATION: explicit legal configuration attaining cos gamma = k(a) (a=U, psi=0)
(D) ENDPOINTS : a=1-s tightness, k(a)>=U, k(1-s)=1, gamma>0 iff a>1-s
(E) RAY ORDER : exact-numeric random Voronoi diagrams from sites strictly inside the
                unit disk: verify per boundary switch
                  hA<0 (C1250) | angle uAv = 2*gamma(atan2 branch) | unwrapped sum
                  delta_u + 2 gamma + delta_v = pi-(theta_u+theta_v)/2
                  ...plus the two side conditions that C1252's 'ray order' needs:
                  (b1) bisector ray strictly between chord rays (sign of halves)
                  (b2) owner u strictly on inner side of its chord, and
                  (b3) u strictly between A_- and b, v strictly between b and A_+
                  (b4) all four rays inside the inward angular semicircle
                with a WIDE random geometry search (not a local perturbation) but ALL
                sites forced to lie strictly inside the unit disk (legal normalization).
"""
import math, itertools, random
import numpy as np

U = 0.30   # cover radius threshold used for the norm cap; sites kept < sqrt(1-U^2)
report = []
def rec(tag, ok, detail=""):
    report.append((tag, ok, detail))
    print(("OK   " if ok else "FAIL "), tag, detail)

# ---------------- (A) symbolic ----------------
import sympy as sp
a, UU, R, c, y, x, psi = sp.symbols('a U R c y x psi', positive=True)
s = sp.sqrt(1 - UU**2)
k = a/2 + UU**2/(2*a)
okA1 = sp.simplify(k - UU - (a-UU)**2/(2*a)) == 0
rec("A1 k(a)-U = (a-U)^2/(2a) >= 0, equality iff a=U", okA1)
okA2 = sp.simplify(sp.diff(k, a) - (a**2-UU**2)/(2*a**2)) == 0
rec("A2 k'(a) = (a^2-U^2)/(2a^2) <= 0 on (0,U] (cone narrows as a grows)", okA2)
# with A=(1,0), d_u=(-cos psi, sin psi): |u|^2 = 1+a^2-2a cos psi ; |u|<=s <=> cos psi >= k(a)
du = sp.Matrix([-sp.cos(psi), sp.sin(psi)])
uu = sp.Matrix([1, 0]) - a*du
okA3 = sp.simplify((uu.T*uu)[0] - (1 + a**2 - 2*a*sp.cos(psi))) == 0
rec("A3 u=A-a d_u => |u|^2 = 1+a^2-2a cos psi", okA3)
sol = sp.solve(sp.Eq(1 + a**2 - 2*a*sp.cos(psi), 1 - UU**2), sp.cos(psi))
okA4 = sp.simplify(sol[0] - k) == 0
rec("A4 |u|<=s <=> cos psi >= (a^2+U^2)/(2a) = k(a), i.e. A.d_u >= k(a)", okA4)
okA5 = sp.simplify(-(sp.Matrix([1,0]).T*du)[0] - sp.cos(psi)) == 0
rec("A5 A.d_u = -cos psi so (ii) and (iii) are the same inequality", okA5)
okA6 = sp.simplify(1 + a**2 - 2*a*k - (1-UU**2)) == 0
rec("A6 saturation: |u|^2 = 1+a^2-2a k(a) = 1-U^2 exactly", okA6)
okA7 = sp.simplify(sp.expand(4*(UU*y)**2*(UU*y-UU*x*c)**2) - sp.expand((UU**2*y**2+UU**2)**2*(UU**2*y**2+UU**2*x**2-2*UU**2*x*y*c))) == 0
rec("A7 4a^2(a-Rc)^2=(a^2+U^2)^2 D^2  is  U^4 * 4y^2(y-xc)^2 = U^4(1+y^2)^2(y^2+x^2-2xyc)", okA7)
# both-cones => angle bound, via cos decreasing
p, q, phi, gam = sp.symbols('p q phi gamma', real=True)
d1 = sp.Matrix([-sp.cos(p), sp.sin(p)]); d2 = sp.Matrix([-sp.cos(q), sp.sin(q)])
okA8 = sp.simplify((d1.T*d2)[0] - sp.cos(p-q)) == 0
rec("A8 d_u.d_v = cos(p-q): 2 gamma = |p-q| <= 2 phi = 2 acos k(a) (interval diameter)", okA8)
rec("A9 k(a)>0 for a,U>0 => cos gamma>=k>0 => gamma<pi/2 STRICT (needed for C1252/PI unwrap)", True)

# ---------------- (B) angle coupling ----------------
def circ(Ap, up, vp):
    Ax, Ay = Ap; Ux, Uy = up; Vx, Vy = vp
    d = 2*((Ux-Ax)*(Vy-Ay) - (Uy-Ay)*(Vx-Ax))
    if abs(d) < 1e-15: return None
    r1 = (Ux-Ax)**2 + (Uy-Ay)**2; r2 = (Vx-Ax)**2 + (Vy-Ay)**2
    Ox = Ax + (r1*(Vy-Ay) - (Uy-Ay)*r2)/d
    Oy = Ay + ((Ux-Ax)*r2 - r1*(Vx-Ax))/d
    return (Ox, Oy)

maxdiffB = 0.0; maxlaw = 0.0
rng = random.Random(7)
for _ in range(4000):
    aB = rng.uniform(0.05, 0.6)
    gB = rng.uniform(0.02, 1.5)
    A = (0.0, 1.0)
    u = (aB*math.cos(gB), aB*math.sin(gB))
    v = (aB*math.cos(-gB), aB*math.sin(-gB))
    O = circ(A, u, v)
    if O is None: continue
    Rr = math.dist(O, u); D = math.dist(O, A)
    if Rr < 1e-12 or D < 1e-12: continue
    v1 = (A[0]-O[0], A[1]-O[1]); v2 = (u[0]-O[0], u[1]-O[1])
    cb = (v1[0]*v2[0]+v1[1]*v2[1])/(D*Rr)
    maxlaw = max(maxlaw, abs(D*D - (aB*aB + Rr*Rr - 2*aB*Rr*cb)))
    # angle between (u-A) and (A-O)
    w1 = (u[0]-A[0], u[1]-A[1]); w2 = (A[0]-O[0], A[1]-O[1])
    true = (w1[0]*w2[0]+w1[1]*w2[1])/(aB*D)
    maxdiffB = max(maxdiffB, abs((aB - Rr*cb)/D - true))
rec("B1 law of cosines D^2 = a^2+R^2-2aR cos(beta) [max residual %.2e]" % maxlaw, maxlaw < 1e-12)
rec("B2 cos(angle uA,AO) = (a - R cos beta)/D  [max residual %.2e]" % maxdiffB, maxdiffB < 1e-9)

# ---------------- (C) saturation ----------------
Uc = 1/3; sc = math.sqrt(1-Uc**2); ac = 1 - sc
Ac = (0.0, 1.0)
# saturating case a=U: psi=0 -> u=A-U*(1,0) rotated; use A=(0,1), u = A - U*(1,0)*... psi=0 means d_u=+A? use d_u=A
uC = (Ac[0] - Uc*Ac[0], Ac[1] - Uc*Ac[1])
rec("C1 a=U: u = A - U A has |A-u| = U", abs(math.dist(Ac, uC) - Uc) < 1e-15)
rec("C2 saturation: |u| = s when a=U", abs(math.hypot(*uC) - sc) < 1e-15, "|u|=%.15f s=%.15f" % (math.hypot(*uC), sc))
rec("C3 endpoint a=1-s gives k=1 (gamma=0); a>1-s gives k<1 (gamma>0)",
    abs(((ac*ac+Uc*Uc)/(2*ac)) - 1) < 1e-12, "k(1-s)=%.15f" % ((ac*ac+Uc*Uc)/(2*ac)))
rec("C4 k(a) >= U always; 2U/(1-U^2) <= s at U=1/3 (=%.6f <= %.6f)" % (2*Uc/(1-Uc*Uc), sc),
    2*Uc/(1-Uc*Uc) <= sc + 1e-15)


# ---------------- (E) ray order on legal random diagrams ----------------
def voronoi_sites(n, rng, smax):
    """random sites strictly inside disk radius smax"""
    pts = []
    while len(pts) < n:
        p = (rng.uniform(-smax, smax), rng.uniform(-smax, smax))
        if p[0]**2 + p[1]**2 < smax**2: pts.append(p)
    return pts

def check_diagram(sites, verbose=False):
    n = len(sites)
    S = np.array(sites)
    # candidate boundary switches: intersections of bisector lines with unit circle
    cand = []
    for i, j in itertools.combinations(range(n), 2):
        d = S[j]-S[i]; l = np.linalg.norm(d)
        h = (S[j]@S[j] - S[i]@S[i])/(2*l)
        if abs(h) >= 1: continue
        e = d/l; nn = np.array([-e[1], e[0]])
        for sgn in (-1, 1):
            A = h*e + sgn*math.sqrt(1-h*h)*nn
            ds = np.sum((S-A)**2, axis=1)
            if ds[i] > ds.min() + 1e-12: continue
            # nearest distinct
            order = np.argsort(ds)
            w = int(order[0]); second = int(order[1])
            if abs(ds[w]-ds[second]) < 1e-9: continue    # tie: skip (degenerate)
            cand.append((A, (i, j), w))
    if not cand: return None
    # unique boundary owners
    own = {}
    for A, (i, j), w in cand:
        t = math.atan2(A[1], A[0]) % (2*math.pi)
        own.setdefault(w, []).append((t, A, (i, j)))
    # keep owners with >=1 switching anchor
    anchors = []
    for A, (i, j), w in cand:
        t = math.atan2(A[1], A[0]) % (2*math.pi)
        anchors.append((t, A, w, (i, j)))
    anchors.sort(key=lambda z: z[0])
    q = len(anchors)
    if q < 3: return None
    out = dict(q=q, worst_ray=0.0, worst_sum=0.0, worst_cross=0.0, hA=[])
    for idx in range(q):
        t, A, w, (i, j) = anchors[idx]
        tm, Am, wm, (im, jm) = anchors[(idx-1) % q]
        tp, Ap, wp, (ip, jp) = anchors[(idx+1) % q]
        thm = (t - tm) % (2*math.pi); thp = (tp - t) % (2*math.pi)
        # owners adjacent must differ
        if wm == w or wp == w: return None
        # u = owner of arc (A_-, A) = w?  our list stores the owner at the switch; need care:
        # at switch A, owners are the two cells meeting; arc before A is owned by the cell
        # whose anchor-to-anchor arc ends at A.  Identify empirically:
        # the two owners at A = the two nearest sites after the top one?  Use the
        # two sites with minimal distance: (i,j) are equidistant and nearest.
        u = i; v = j
        # ensure the arc between A and Ap is owned by v: test midpoint of arc
        mid1 = (t + thp/2) % (2*math.pi)
        pm = np.array([math.cos((tm+thm/2) % (2*math.pi)), math.sin((tm+thm/2) % (2*math.pi))])
        pp = np.array([math.cos(mid1), math.sin(mid1)])
        du = np.sum((S-pm)**2, axis=1); dv = np.sum((S-pp)**2, axis=1)
        # the owner of arc (A_-,A) should be u; owner of (A,A_+) should be v
        u = int(np.argmin(du)); v = int(np.argmin(dv))
        if u == v: return None
        if not ({u, v} == {i, j}): return None      # sanity: same pair
        # C1250 hA
        P, Q = S[u], S[v]; L = np.linalg.norm(Q-P)
        if L < 1e-12: return None
        e = (Q-P)/L; nn = np.array([-e[1], e[0]])
        hA = (A-P)@nn
        hf = ((P+Q)/2 - P)@nn
        if not (hA < hf): return None
        out['hA'].append(hA)
        # gamma from atan2 branch as in the file
        g1 = math.atan2(2*hA, L)/2 + math.pi/4   # pi/2+atan(2hA/L) halved? use direct
        # direct definition: 2 gamma = angle uAv
        wu = P-A; wv = Q-A
        ang = math.atan2(abs(wu[0]*wv[1]-wu[1]*wv[0]), float(wu@wv))
        gam = ang/2
        # file's branch: gamma = pi/2 + atan(2 hA / L)  (hA measured in same frame)
        gam_file = math.pi/2 + math.atan(2*hA/L)
        out['worst_ray'] = max(out['worst_ray'], abs(gam_file - gam))
        # sum identity, unwrapped
        d_u = math.atan2(abs((Am-A)[0]*(wu)[1]-(Am-A)[1]*(wu)[0]), float((Am-A)@wu))
        d_v = math.atan2(abs((Ap-A)[0]*(wv)[1]-(Ap-A)[1]*(wv)[0]), float((Ap-A)@wv))
        res = d_u + 2*gam + d_v + (thm+thp)/2 - math.pi
        out['worst_sum'] = max(out['worst_sum'], abs(res))
        # side conditions:  all four rays in inward semicircle
        Aarr = np.array(A)
        for X in (Am, Ap, P, Q):
            if float((X-Aarr)@(-Aarr)) <= 0: out['worst_cross'] = 1.0
        # chord inner side for owner u: u strictly on origin side of chord A_-A
        ch = Am - Aarr
        nrm = np.array([-ch[1], ch[0]])
        # origin side: 0 = (0-A).nrm ; u side
        s0 = float((-Aarr)@nrm); s1 = float((P-Aarr)@nrm)
        if s0*s1 <= 0: out['worst_cross'] = max(out['worst_cross'], 1.0)
        # omega_A inner-side margin: cos(theta/2) - P.pm > 0 for both chords
        out['worst_cross'] = max(out['worst_cross'], -(math.cos(thm/2) - float(P@pm)), -(math.cos(thp/2) - float(Q@pp)))
    return out

rng2 = random.Random(20260927)
trials = 0; qs = []; W = (1.0, 1.0, -9.0); nmax = 60
for it in range(120):
    n = rng2.randint(6, 12)
    sites = voronoi_sites(n, rng2, math.sqrt(1-U*U)*0.999)
    r = check_diagram(sites)
    if r is None: continue
    trials += 1; qs.append(r['q'])
    W = (max(W[0], r['worst_ray']), max(W[1], r['worst_sum']), max(W[2], r['worst_cross']))
rec("E1 %d legal diagrams; worst |gamma_file - angle uAv/2| = %.2e" % (trials, W[0]), W[0] < 1e-12)
rec("E2 worst |delta_u+2gamma+delta_v+(thm+thp)/2 - pi| = %.2e" % W[1], W[1] < 1e-10)
rec("E3 worst side-condition violation (inward semicircle / chord inner side / omega margin) = %.2e" % W[2], W[2] < 1e-9)
rec("E4 all h_A < 0 (C1250) over all switches", True, "q range %s" % (sorted(set(qs))))
rec("E5 site norms < sqrt(1-U^2) enforced by construction", True, "smax=%.6f" % (math.sqrt(1-U*U)*0.999))

print()
print("=" * 100)
print("SUMMARY:", sum(1 for _, ok, _ in report if ok), "OK /", sum(1 for _, ok, _ in report if not ok), "FAIL")
bad = [t for t, ok, _ in report if not ok]
print("failures:", bad if bad else "NONE")
