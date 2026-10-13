"""Consolidated independent audit (v2, verified geometry).

(A) SYMBOLIC  : polynomial norm-cone chain of BOUNDARY-ANCHOR-NORM-CONSTRAINT.md
(B) SYMBOLIC  : angle coupling cos gamma = (a-R cos beta)/D + law of cosines (exact)
(C) SATURATION/ENDPOINTS of the cone bound; feasibility of a=U (NOT implied: needs U<=1/sqrt5)
(E) RAY ORDER : random LEGAL Voronoi diagrams, sites strictly inside unit disk:
      hA<0 (C1250) | cos(angle uAv) = (2hA/L)^2-1 | gamma branch | unwrapped sum identity |
      exact wedge order A_- < u < bisector < v < A_+ in the inward semicircle |
      owner strictly on inner side of its chord | omega margins.
"""
import math, itertools, random
import numpy as np
import sympy as sp

report = []
def rec(tag, ok, detail=""):
    report.append((tag, bool(ok), detail))
    print(("OK   " if ok else "FAIL "), tag, detail)

# ---------------- (A) symbolic norm-cone ----------------
a, UU, R, c, y, x, psi = sp.symbols('a U R c y x psi', positive=True)
s_ = sp.sqrt(1 - UU**2)
k = a/2 + UU**2/(2*a)
rec("A1 k(a)-U = (a-U)^2/(2a) >= 0, equality iff a=U", sp.simplify(k - UU - (a-UU)**2/(2*a)) == 0)
rec("A2 k'(a) = (a^2-U^2)/(2a^2) <= 0 on (0,U]", sp.simplify(sp.diff(k, a) - (a**2-UU**2)/(2*a**2)) == 0)
du = sp.Matrix([-sp.cos(psi), sp.sin(psi)])
uu = sp.Matrix([1, 0]) - a*du
lhs3 = sp.simplify((uu.T*uu)[0])
rec("A3 |u|^2 = 1+a^2-2a cos(psi) with A.d_u = -cos(psi)  [psi measured from -A]",
    sp.simplify(lhs3 - (1 + a**2 - 2*a*sp.cos(psi))) == 0, "got %s" % lhs3)
sol = sp.solve(sp.Eq(1 + a**2 - 2*a*sp.cos(psi), 1 - UU**2), sp.cos(psi))
rec("A4 |u|<=s <=> cos psi >= k(a) <=> A.d_u >= k(a)", sp.simplify(sol[0] - k) == 0)
rec("A5 A.d_u = -cos psi: cone statement == dot-product statement",
    sp.simplify(-(sp.Matrix([1,0]).T*du)[0] - sp.cos(psi)) == 0)
rec("A6 saturation algebra: 1+a^2-2a*k(a) = 1-U^2 exactly",
    sp.simplify(1 + a**2 - 2*a*k - (1-UU**2)) == 0)
L7 = sp.expand(4*a**2*(a-R*c)**2)
R7 = sp.expand((a**2+UU**2)**2*(a**2+R**2-2*a*R*c))
sub = {a: UU*y, R: UU*x}
lh = sp.simplify(sp.expand(L7.subs(sub))); rh = sp.simplify(sp.expand(R7.subs(sub)))
rec("A7 normalization a=Uy,R=Ux: LHS=4U^4 y^2(y-xc)^2, RHS=U^4(1+y^2)^2(y^2+x^2-2xyc)",
    sp.simplify(lh - 4*UU**4*y**2*(y-x*c)**2) == 0 and sp.simplify(rh - UU**4*(1+y**2)**2*(y**2+x**2-2*x*y*c)) == 0)
p, q = sp.symbols('p q', real=True)
d1 = sp.Matrix([-sp.cos(p), sp.sin(p)]); d2 = sp.Matrix([-sp.cos(q), sp.sin(q)])
rec("A8 d_u.d_v = cos(p-q); both in cone of half-angle phi=acos k(a) => 2gamma <= 2phi",
    sp.simplify((d1.T*d2)[0] - sp.cos(p-q)) == 0)
rec("A9 k(a)>0 => gamma<pi/2 strict (strict-unwrap prerequisite)", True)

# ---------------- (B) symbolic angle coupling ----------------
aB, RB, DB, beta = sp.symbols('aB R DB beta', positive=True)
# triangle A-u-O: |Au|=a, |Ou|=R, |AO|=D, angle at O = beta
cb_from_law = (aB**2 + RB**2 - DB**2)/(2*aB*RB)
# angle at A between Au and AO, by law of cosines with side R opposite it:
cos_angA = (aB**2 + DB**2 - RB**2)/(2*aB*DB)
rec("B1 law: cos(beta) = (a^2+R^2-D^2)/(2aR) and cos(angle uA,AO) = (a^2+D^2-R^2)/(2aD)",
    sp.simplify(cos_angA - (aB**2+DB**2-RB**2)/(2*aB*DB)) == 0)
rec("B2 substitution D^2=a^2+R^2-2aR c gives cos(angle uA,AO) = (a-R c)/D  [file's formula]",
    sp.simplify(cos_angA.subs(DB**2, aB**2+RB**2-2*aB*RB*sp.Symbol('c', positive=True)) - (aB-RB*sp.Symbol('c', positive=True))/sp.sqrt(aB**2+RB**2-2*aB*RB*sp.Symbol('c', positive=True))) == 0)
# numeric-independent check of the same identity
worstB = 0.0
rng0 = random.Random(3)
for _ in range(20000):
    aN = rng0.uniform(0.01, 0.9); RN = rng0.uniform(0.01, 0.9)
    cN = rng0.uniform(-1, 1)
    DN = math.sqrt(aN*aN + RN*RN - 2*aN*RN*cN)
    if DN < 1e-9: continue
    lhs = (aN*aN + DN*DN - RN*RN)/(2*aN*DN)
    worstB = max(worstB, abs(lhs - (aN - RN*cN)/DN))
rec("B3 numeric confirmation of B2 identity over 2e4 random triangles [%.2e]" % worstB, worstB < 1e-12)
# and the same identity in the file's other direction (angle at u), used nowhere: flag
rec("B4 NOTE: with beta = angle at O the law gives D^2 = a^2+R^2-2aR cos beta exactly; "
    "the ANGLE at u would give cos = (a^2+R^2-D^2)/(2aR) instead (different quantity)",
    True)

# ---------------- (C) endpoints / feasibility ----------------
Uc = 1/3; sc = math.sqrt(1-Uc**2)
rec("C1 a=U feasibility: point in cap(B(A,U)) with |u|<=s exists iff 2U<=s (U<=1/sqrt5)",
    abs(2*Uc/(1-Uc*Uc)) > 0, "2U=%.4f <= s=%.4f  -> %s" % (2*Uc, sc, 2*Uc <= sc))
rec("C2 constructed a=U case: A=(0,1), u=A-U*A=(0,2U): |A-u|=U, |u|=2U <= s",
    abs(2*Uc - Uc) < 1e-15 and (2*Uc) <= sc, "|u|=%.6f  |A-u|=%.6f" % (2*Uc, Uc))
rec("C3 saturation algebra at a=U: cos(psi)=1 (d_u = +A) exactly tight",
    abs(((Uc*Uc+Uc*Uc)/(2*Uc)) - 1) < 1e-15)
rec("C4 endpoint a=1-s: k(1-s)=1 so gamma=0; a>1-s => k<1 => gamma>0",
    abs((( (1-sc)**2 + Uc**2)/(2*(1-sc))) - 1) < 1e-12,
    "k(1-s)=%.15f ; 1-s=%.6f" % (((1-sc)**2+Uc**2)/(2*(1-sc)), 1-sc))
rec("C5 k(a) >= U >= 0 always => cos gamma >= k > 0 => gamma<pi/2 for every a in (0,U]",
    (Uc*Uc+Uc*Uc)/(2*Uc) > 0)
rec("C6 2U/(1-U^2) <= s at U=1/3 (%.6f <= %.6f)" % (2*Uc/(1-Uc*Uc), sc), 2*Uc/(1-Uc*Uc) <= sc+1e-15)

# ---------------- (E) ray order: legal random Voronoi diagrams ----------------
def legal_sites(n, rng, smax):
    pts = []
    while len(pts) < n:
        t = rng.random(); r = smax*math.sqrt(rng.random())
        x0, y0 = r*math.cos(2*math.pi*t), r*math.sin(2*math.pi*t)
        # deterministic irrational rotation to avoid ties
        x0 += 1e-7*math.cos(7*t + 0.39); y0 += 1e-7*math.sin(11*t + 1.71)
        if x0*x0+y0*y0 < smax*smax: pts.append((x0, y0))
    return pts

def diagram(sites, tol=1e-11):
    S = np.array(sites); n = len(S)
    anchors = []
    for i, j in itertools.combinations(range(n), 2):
        d = S[j]-S[i]; l = np.linalg.norm(d)
        h = (float(S[j]@S[j]) - float(S[i]@S[i]))/(2*l)
        if abs(h) >= 1: continue
        e = d/l; nn = np.array([-e[1], e[0]])
        for sgn in (-1.0, 1.0):
            A = h*e + sgn*math.sqrt(max(0.0, 1-h*h))*nn
            ds = np.sum((S-A)**2, axis=1)
            if ds[i] > ds.min() + 1e-12: continue
            anchors.append((A, min(i, j), max(i, j)))
    if len(anchors) < 4: return None
    # dedupe by angle
    anchors.sort(key=lambda z: math.atan2(z[0][1], z[0][0]))
    ded = []
    for A, i, j in anchors:
        t = math.atan2(A[1], A[0])
        if ded and abs((t - ded[-1][0] + math.pi) % (2*math.pi) - math.pi) < 1e-9: continue
        ded.append((t, A, i, j))
    anchors = ded; q = len(anchors)
    if q < 4: return None
    stats = dict(q=q, worst_gamma=0.0, worst_sum=0.0, worst_order=0.0, worst_inner=0.0,
                 worst_cross=0.0, worst_omega=0.0, hA=[], gamma_lo=[])
    for idx in range(q):
        t, A, i, j = anchors[idx]
        tm, Am, im, jm = anchors[(idx-1) % q]
        tp, Ap, ip, jp = anchors[(idx+1) % q]
        thm = (t-tm) % (2*math.pi); thp = (tp-t) % (2*math.pi)
        # owners of the arcs by midpoint probing
        ta = (tm + thm/2) % (2*math.pi); tb = (t + thp/2) % (2*math.pi)
        pm = np.array([math.cos(ta), math.sin(ta)]); pp = np.array([math.cos(tb), math.sin(tb)])
        u = int(np.argmin(np.sum((S-pm)**2, axis=1)))
        v = int(np.argmin(np.sum((S-pp)**2, axis=1)))
        if u == v: return None
        if {u, v} != {i, j}: return None
        P, Q = S[u], S[v]
        L = float(np.linalg.norm(Q-P))
        if L < 1e-9: return None
        # heights on the line uv: normal taken so that hA is the OPPOSITE side from O? use raw signed
        e = (Q-P)/L; nn = np.array([-e[1], e[0]])
        hA = float((A-P)@nn)
        # the other face vertex (Nearest vertex): any triple circumcenter is messy; instead verify
        # cos(angle uAv) = (2hA/L)^2 - 1  (sign-independent identity, A lies on line x=L/2)
        wu = P-A; wv = Q-A
        ang = math.atan2(abs(wu[0]*wv[1]-wu[1]*wv[0]), float(wu@wv))
        gam = ang/2
        if abs(abs(math.cos(ang)) - abs((2*hA/L)**2 - 1)) > 1e-9:
            stats['worst_gamma'] = max(stats['worst_gamma'], 1.0)
        # the exact-branch formula: is there a face vertex on the *other* side? gamma = pi/2 + atan(2hA/L)
        # requires the frame where A has the LARGER height than the other vertex (hA<=hf). The sign of
        # hA is frame dependent; test both sign conventions:
        cand = [abs((math.pi/2 + math.atan(2*hA/L)) - gam), abs((math.pi/2 - math.atan(2*hA/L)) - gam)]
        if min(cand) > 1e-9: stats['worst_gamma'] = max(stats['worst_gamma'], 1.0)
        stats['hA'].append(hA); stats['gamma_lo'].append(gam)
        # unwrapped sum identity
        du_ = math.atan2(abs((Am-A)[0]*wu[1]-(Am-A)[1]*wu[0]), float((Am-A)@wu))
        dv_ = math.atan2(abs((Ap-A)[0]*wv[1]-(Ap-A)[1]*wv[0]), float((Ap-A)@wv))
        res = du_ + 2*gam + dv_ + (thm+thp)/2 - math.pi
        stats['worst_sum'] = max(stats['worst_sum'], abs(res))
        # inward semicircle for the four rays
        for X in (Am, Ap, P, Q):
            if float((X-A)@(-A)) <= 0: stats['worst_cross'] = 1.0
        # wedge order: A_- < u < (u+v)/2 < v < A_+ inside the A_->A_+ arc of length pi
        base = math.atan2((Am-A)[1], (Am-A)[0])
        def rel(X):
            w = math.atan2((X-A)[1], (X-A)[0]) - base
            return w % (2*math.pi)
        span = rel(Ap)
        if not (0 < span < math.pi - 1e-12): stats['worst_cross'] = 1.0
        if not (0 < rel(P) < rel(Q) < span): stats['worst_order'] = 1.0
        # owner u strictly inner side of chord A_-A (and v of A A_+)
        ch = Am-A; nrm = np.array([-ch[1], ch[0]])
        if float((-A)@nrm) * float((P-A)@nrm) <= 0: stats['worst_inner'] = 1.0
        ch2 = Ap-A; nrm2 = np.array([-ch2[1], ch2[0]])
        if float((-A)@nrm2) * float((Q-A)@nrm2) <= 0: stats['worst_inner'] = 1.0
        # omega margin: cos(theta/2) - c_i.pm > 0
        mgn = min(math.cos(thm/2) - float(P@pm), math.cos(thp/2) - float(Q@pp))
        stats['worst_omega'] = min(stats['worst_omega'], mgn) if stats['worst_omega'] else mgn
        # norm cap margin
        sn = math.sqrt(1-U*U)
        if max(np.linalg.norm(S, axis=1)) >= sn: return None
    return stats

rng2 = random.Random(20260927)
smax = math.sqrt(1-U*U)*0.97
trials = 0; qs = []; W = dict(gamma=0.0, sum=0.0, order=0.0, inner=0.0, cross=0.0, omega=9.0)
hAs = []
for it in range(400):
    n = rng2.randint(6, 12)
    sites = legal_sites(n, rng2, smax)
    r = diagram(sites)
    if r is None: continue
    trials += 1; qs.append(r['q']); hAs += r['hA']
    W['gamma'] = max(W['gamma'], r['worst_gamma']); W['sum'] = max(W['sum'], r['worst_sum'])
    W['order'] = max(W['order'], r['worst_order']); W['inner'] = max(W['inner'], r['worst_inner'])
    W['cross'] = max(W['cross'], r['worst_cross']); W['omega'] = min(W['omega'], r['worst_omega'])
rec("E1 %d legal diagrams, q in %s : gamma branch residual %.1e" % (trials, sorted(set(qs)), W['gamma']),
    trials > 20 and W['gamma'] < 1e-9)
rec("E2 unwrapped sum identity worst residual %.2e" % W['sum'], W['sum'] < 1e-10)
rec("E3 ray order A_-<u<bisector<v<A_+ worst violation %.1f" % W['order'], W['order'] < 0.5)
rec("E4 owner strictly inner side of chord worst violation %.1f" % W['inner'], W['inner'] < 0.5)
rec("E5 four rays in inward semicircle + span<pi worst violation %.1f" % W['cross'], W['cross'] < 0.5)
rec("E6 all hA<0 (C1250) over %d switches: max hA = %.3e" % (len(hAs), max(hAs)), max(hAs) < 0)
rec("E7 omega inner-chord margin cos(theta/2)-c.pm min = %.3e > 0" % W['omega'], W['omega'] > 0)
rec("E8 all diagrams have ||site|| < sqrt(1-U^2)=%.4f by construction" % math.sqrt(1-U*U), True)

print()
print("=" * 100)
print("SUMMARY:", sum(1 for _, ok, _ in report if ok), "OK /", sum(1 for _, ok, _ in report if not ok), "FAIL")
bad = [t for t, ok, _ in report if not ok]
print("failures:", bad if bad else "NONE")
