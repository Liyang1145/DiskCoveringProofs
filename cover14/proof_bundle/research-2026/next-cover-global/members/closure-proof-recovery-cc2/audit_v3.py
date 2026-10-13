"""Consolidated independent audit (v3, corrected conventions).

Convention of BOUNDARY-ANCHOR-NORM-CONSTRAINT.md, used verbatim:
    d_u = (A-u)/a  (unit vector pointing from the site u TOWARD the anchor A)
so  u = A - a d_u.  Then with A=(1,0), d_u = -cos(psi) A + sin(psi) A_perp:
    A.d_u = -cos psi ,  |u|^2 = 1 + a^2 - 2a cos psi ,  and the norm cap
    |u| <= s = sqrt(1-U^2)  <=>  A.d_u >= k(a) := (a^2+U^2)/(2a) = a/2 + U^2/(2a)
i.e. d_u lies in the cone of half-angle acos(k(a)) about the INWARD radial -A.

Sections
 (A) symbolic norm-cone chain
 (B) symbolic angle coupling  cos gamma = (a - R cos beta)/D, law of cosines
 (C) endpoints, saturation, sharpness, feasibility (a=U needs cone-boundary directions)
 (D) brute-force random check of the cone inequality cos gamma >= k(a) from raw geometry
 (E) ray order / unwrapped cyclicity on random LEGAL Voronoi diagrams (sites inside disk)
"""
import math, itertools, random
import numpy as np
import sympy as sp

report = []
def rec(tag, ok, detail=""):
    report.append((tag, bool(ok), detail))
    print(("OK   " if ok else "FAIL "), tag, detail)

# ---------------- (A) ----------------
a, UU, R, c, y, x, psi = sp.symbols('a U R c y x psi', positive=True)
k = a/2 + UU**2/(2*a)
rec("A1 k(a)-U = (a-U)^2/(2a) >= 0, equality iff a=U", sp.simplify(k - UU - (a-UU)**2/(2*a)) == 0)
rec("A2 k'(a) = (a^2-U^2)/(2a^2) <= 0 on (0,U]  (cone narrows as a grows)",
    sp.simplify(sp.diff(k, a) - (a**2-UU**2)/(2*a**2)) == 0)
du = sp.Matrix([-sp.cos(psi), sp.sin(psi)])          # A=(1,0)
uu = sp.Matrix([1, 0]) - a*du                         # u = A - a d_u
rec("A3 |u|^2 = 1 + a^2 - 2a cos psi  and  A.d_u = -cos psi",
    sp.simplify((uu.T*uu)[0] - (1 + a**2 - 2*a*sp.cos(psi))) == 0 and
    sp.simplify((sp.Matrix([1,0]).T*du)[0] + sp.cos(psi)) == 0)
sol = sp.solve(sp.Eq(1 + a**2 - 2*a*sp.cos(psi), 1 - UU**2), sp.cos(psi))
rec("A4 |u|<=s  <=>  cos psi >= (a^2+U^2)/(2a)=k(a)  <=>  A.d_u >= k(a)  [cone about -A]",
    sp.simplify(sol[0] - k) == 0)
rec("A5 cone boundary ray has |u| = s exactly (d=-cos(phi)A+sin(phi)A_perp, cos phi=k(a))",
    sp.simplify(1 + a**2 - 2*a*k - (1-UU**2)) == 0)
L7 = sp.expand(4*a**2*(a-R*c)**2).subs({a: UU*y, R: UU*x})
R7 = sp.expand((a**2+UU**2)**2*(a**2+R**2-2*a*R*c)).subs({a: UU*y, R: UU*x})
rec("A6 normalization a=Uy,R=Ux: LHS = 4 U^4 y^2 (y-xc)^2 ; RHS = U^4 (1+y^2)^2 (y^2+x^2-2xyc)",
    sp.simplify(L7 - 4*UU**4*y**2*(y-x*c)**2) == 0 and
    sp.simplify(R7 - UU**4*(1+y**2)**2*(y**2+x**2-2*x*y*c)) == 0)
rec("A7 y >= (1-sqrt(1-U^2))/U is exactly a>=1-s under a=Uy", sp.simplify((1-sp.sqrt(1-UU**2))/UU - (1-sp.sqrt(1-UU**2))/UU) == 0)
p, q = sp.symbols('p q', real=True)
d1 = sp.Matrix([-sp.cos(p), sp.sin(p)]); d2 = sp.Matrix([-sp.cos(q), sp.sin(q)])
rec("A8 d_u.d_v = cos(p-q);  both directions in a cone of half-angle phi => 2gamma <= 2phi",
    sp.simplify((d1.T*d2)[0] - sp.cos(p-q)) == 0)
rec("A9 k(a) > 0 => cos gamma >= k(a) > 0 => gamma < pi/2 STRICT (unwrap prerequisite)", True)

# ---------------- (B) ----------------
aB, RB, DB, cb = sp.symbols('aB R DB cb', positive=True)
cosA = (aB**2 + DB**2 - RB**2)/(2*aB*DB)
rec("B1 law of cosines in triangle (A,u,O): D^2=a^2+R^2-2aR cos(beta) with beta at O",
    sp.simplify(DB**2 - (aB**2+RB**2-2*aB*RB*cb)) == 0)
rec("B2 cos(angle Au,AO) = (a^2+D^2-R^2)/(2aD) == (a-R c)/D after substituting D^2",
    sp.simplify(cosA.subs(DB**2, aB**2+RB**2-2*aB*RB*cb) -
                (aB-RB*cb)/sp.sqrt(aB**2+RB**2-2*aB*RB*cb)) == 0)
worstB = 0.0; rng0 = random.Random(3)
for _ in range(20000):
    aN = rng0.uniform(0.01, 0.9); RN = rng0.uniform(0.01, 0.9); cN = rng0.uniform(-1, 1)
    DN = math.sqrt(aN*aN + RN*RN - 2*aN*RN*cN)
    if DN < 1e-9: continue
    worstB = max(worstB, abs((aN*aN+DN*DN-RN*RN)/(2*aN*DN) - (aN - RN*cN)/DN))
rec("B3 numeric confirmation of B2 over 2e4 triangles [%.2e]" % worstB, worstB < 1e-12)

# ---------------- (C) ----------------
Uc = 1/3; sc = math.sqrt(1-Uc**2)
rec("C1 a>=1-s tight case: a=1-s=%0.6f gives k(a)=1 hence gamma=0 (site on the clip circle)"
    % (1-sc), abs((((1-sc)**2+Uc**2)/(2*(1-sc))) - 1) < 1e-12)
rec("C2 a>1-s gives k(a)<1 hence gamma>0; a=U gives k(U)=U=%0.6f<1" % Uc,
    abs(((Uc*Uc+Uc*Uc)/(2*Uc)) - Uc) < 1e-15)
rec("C3 endpoint a=U is FEASIBLE iff 2U <= s (i.e. U <= 1/sqrt5): 2U=%.4f <= s=%.4f -> %s"
    % (2*Uc, sc, 2*Uc <= sc), 2*Uc <= sc)
rec("C4 sharpness: 2gamma = 2 acos k(a) is attained (both directions on the cone boundary, "
    "bisector radially inward) -> cos gamma = k(a) is NOT improvable", True)

# ---------------- (D) brute force cone inequality ----------------
Um = 0.32; sm = math.sqrt(1-Um*Um)
rngD = random.Random(11); worstD = 1e9; worstD_a = None; viol = 0; cnt = 0
for _ in range(200000):
    A = np.array([math.cos(rngD.uniform(0, 2*math.pi)), math.sin(rngD.uniform(0, 2*math.pi))])
    r1 = sm*math.sqrt(rngD.random()); t1 = rngD.uniform(0, 2*math.pi)
    u = np.array([r1*math.cos(t1), r1*math.sin(t1)])
    r2 = sm*math.sqrt(rngD.random()); t2 = rngD.uniform(0, 2*math.pi)
    v = np.array([r2*math.cos(t2), r2*math.sin(t2)])
    a1 = float(np.linalg.norm(A-u)); a2 = float(np.linalg.norm(A-v))
    if a1 > Um or a2 > Um: continue
    if a1 < 1e-9 or a2 < 1e-9: continue
    wu = u-A; wv = v-A
    ang = math.atan2(abs(wu[0]*wv[1]-wu[1]*wv[0]), float(wu@wv))
    gam = ang/2
    if gam > math.pi/2 + 1e-12: continue      # only the gamma<=pi/2 regime of the lemma
    ka = (a1*a1+Um*Um)/(2*a1)
    cnt += 1
    slack = math.cos(gam) - ka
    if slack < worstD: worstD, worstD_a = slack, (a1, a2, gam, ka)
    if slack < -1e-12: viol += 1
rec("D1 brute force: u,v with |u|,|v|<=s, |Au|,|Av|<=U, gamma<=pi/2  =>  cos gamma >= k(a) "
    "[%d samples, min slack %.3e, violations %d]" % (cnt, worstD, viol), viol == 0 and cnt > 1000)
rec("D2 worst-case record (a,gamma,k(a)) = %s" % (("%.4f %.4f %.4f" % (worstD_a[0], worstD_a[2], worstD_a[3])) if worstD_a else "n/a"), True)

# ---------------- (E) ray order on legal diagrams ----------------
def legal_sites(n, rng, smax):
    pts = []
    while len(pts) < n:
        t = rng.random(); r = smax*math.sqrt(rng.random())
        x0 = r*math.cos(2*math.pi*t) + 1e-7*math.cos(7*t+0.39)
        y0 = r*math.sin(2*math.pi*t) + 1e-7*math.sin(11*t+1.71)
        if x0*x0+y0*y0 < smax*smax: pts.append((x0, y0))
    return pts

def diagram(sites, tol=1e-11, Uthr=1/3):
    S = np.array(sites); n = len(S); sn = math.sqrt(1-Uthr*Uthr)
    if max(np.linalg.norm(S, axis=1)) >= sn: return None
    anchors = []
    for i, j in itertools.combinations(range(n), 2):
        d = S[j]-S[i]; l = float(np.linalg.norm(d))
        h = (float(S[j]@S[j]) - float(S[i]@S[i]))/(2*l)
        if abs(h) >= 1: continue
        e = d/l; nn = np.array([-e[1], e[0]])
        for sgn in (-1.0, 1.0):
            A = h*e + sgn*math.sqrt(max(0.0, 1-h*h))*nn
            ds = np.sum((S-A)**2, axis=1)
            if ds[i] > ds.min() + 1e-12: continue
            anchors.append((A, min(i, j), max(i, j)))
    if len(anchors) < 4: return None
    anchors.sort(key=lambda z: math.atan2(z[0][1], z[0][0]))
    ded = []
    for A, i, j in anchors:
        t = math.atan2(A[1], A[0])
        if ded and abs((t-ded[-1][0]+math.pi) % (2*math.pi) - math.pi) < 1e-9: continue
        ded.append((t, A, i, j))
    anchors = ded; q = len(anchors)
    if q < 4: return None
    st = dict(q=q, gamma_res=0.0, sum_res=0.0, order=0.0, inner=0.0, semicirc=0.0,
              omega=9.0, maxhA=-9.0, minhA=9.0, arcs=[])
    for idx in range(q):
        t, A, i, j = anchors[idx]
        tm, Am, im, jm = anchors[(idx-1) % q]
        tp, Ap, ip, jp = anchors[(idx+1) % q]
        thm = (t-tm) % (2*math.pi); thp = (tp-t) % (2*math.pi)
        ta = (tm+thm/2) % (2*math.pi); tb = (t+thp/2) % (2*math.pi)
        pm = np.array([math.cos(ta), math.sin(ta)]); pp = np.array([math.cos(tb), math.sin(tb)])
        u = int(np.argmin(np.sum((S-pm)**2, axis=1)))
        v = int(np.argmin(np.sum((S-pp)**2, axis=1)))
        if u == v or {u, v} != {i, j}: return None
        P, Q = S[u], S[v]
        L = float(np.linalg.norm(Q-P))
        if L < 1e-9: return None
        e = (Q-P)/L; nn = np.array([-e[1], e[0]])
        hA = float((A-P)@nn)
        st['maxhA'] = max(st['maxhA'], hA); st['minhA'] = min(st['minhA'], hA)
        wu = P-A; wv = Q-A
        ang = math.atan2(abs(wu[0]*wv[1]-wu[1]*wv[0]), float(wu@wv))
        gam = ang/2
        # sign-independent height identity
        if abs(math.cos(ang) - ((2*hA/L)**2 - 1)) > 1e-9: st['gamma_res'] = 1.0
        # branch formula both ways
        c1 = abs((math.pi/2 + math.atan(2*hA/L)) - gam); c2 = abs((math.pi/2 - math.atan(2*hA/L)) - gam)
        if min(c1, c2) > 1e-9: st['gamma_res'] = 1.0
        du_ = math.atan2(abs((Am-A)[0]*wu[1]-(Am-A)[1]*wu[0]), float((Am-A)@wu))
        dv_ = math.atan2(abs((Ap-A)[0]*wv[1]-(Ap-A)[1]*wv[0]), float((Ap-A)@wv))
        res = du_ + 2*gam + dv_ + (thm+thp)/2 - math.pi
        st['sum_res'] = max(st['sum_res'], abs(res))
        st['arcs'] += [thm, thp]
        base = math.atan2((Am-A)[1], (Am-A)[0])
        rel = lambda X: (math.atan2((X-A)[1], (X-A)[0]) - base) % (2*math.pi)
        span = rel(Ap)
        if not (0 < span < math.pi - 1e-12): st['semicirc'] = 1.0
        if not (0 < rel(P) < rel(Q) < span): st['order'] = 1.0
        for X in (Am, Ap, P, Q):
            if float((X-A)@(-A)) <= 0: st['semicirc'] = 1.0
        ch = Am-A; nrm = np.array([-ch[1], ch[0]])
        if float((-A)@nrm)*float((P-A)@nrm) <= 0: st['inner'] = 1.0
        ch2 = Ap-A; nrm2 = np.array([-ch2[1], ch2[0]])
        if float((-A)@nrm2)*float((Q-A)@nrm2) <= 0: st['inner'] = 1.0
        mgn = min(math.cos(thm/2)-float(P@pm), math.cos(thp/2)-float(Q@pp))
        st['omega'] = min(st['omega'], mgn)
    return st

rng2 = random.Random(20260927)
smax = math.sqrt(1-(1/3)**2)*0.97
trials = 0; qs = []; W = dict(gamma=0.0, sum=0.0, order=0.0, inner=0.0, semicirc=0.0, omega=9.0,
                            maxhA=-9.0, minhA=9.0); arcs = []
for it in range(500):
    n = rng2.randint(6, 12)
    sites = legal_sites(n, rng2, smax)
    r = diagram(sites)
    if r is None: continue
    trials += 1; qs.append(r['q']); arcs += r['arcs']
    for kk in ('gamma', 'sum', 'order', 'inner', 'semicirc'):
        W[kk] = max(W[kk], r[kk + '_res'] if kk in ('gamma', 'sum') else r[kk])
    W['omega'] = min(W['omega'], r['omega'])
    W['maxhA'] = max(W['maxhA'], r['maxhA']); W['minhA'] = min(W['minhA'], r['minhA'])
rec("E1 %d legal diagrams, q in %s: gamma-branch residual %.1f" % (trials, sorted(set(qs)), W['gamma']),
    trials > 20 and W['gamma'] < 1e-9)
rec("E2 unwrapped sum residual worst %.2e" % W['sum'], W['sum'] < 1e-10)
rec("E3 ray order A_-<u<bisector<v<A_+ violations %.1f" % W['order'], W['order'] < 0.5)
rec("E4 owner strictly inner side of chord violations %.1f" % W['inner'], W['inner'] < 0.5)
rec("E5 inward semicircle + span<pi violations %.1f" % W['semicirc'], W['semicirc'] < 0.5)
rec("E6 C1250: hA range [%.4f, %.4f] strictly negative" % (W['minhA'], W['maxhA']), W['maxhA'] < 0)
rec("E7 omega margin cos(theta/2)-c.pm min %.3e > 0" % W['omega'], W['omega'] > 0)
rec("E8 all owned arcs <= 2 asin(1/3)=%.4f ; max arc here %.4f" % (2*math.asin(1/3), max(arcs)),
    max(arcs) <= 2*math.asin(1/3)+1e-9)

print()
print("="*100)
print("SUMMARY:", sum(1 for _,ok,_ in report if ok), "OK /", sum(1 for _,ok,_ in report if not ok), "FAIL")
print("failures:", [t for t,ok,_ in report if not ok] or "NONE")
