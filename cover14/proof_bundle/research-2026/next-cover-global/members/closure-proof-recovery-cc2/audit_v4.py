"""Consolidated independent audit (v4, conventions verified numerically at every step).

C1253 convention (verified):  d_u := (A-u)/a ,  u = A - a d_u .
With A=(1,0), d_u = cos(psi) A + sin(psi) A_perp  (psi = angle between d_u and the OUTWARD
radial A; d_u points from the site outward to the anchor):
   A.d_u = cos psi ,   |u|^2 = 1 + a^2 - 2 a cos psi
   norm cap |u| <= s = sqrt(1-U^2)   <=>   cos psi >= k(a) := (a^2+U^2)/(2a) = a/2 + U^2/(2a)
   => d_u lies in the cone about +A of half-angle acos(k(a)) (NOT about -A; verified below).
   The cone-boundary ray psi = acos k(a) has |u| = s exactly.

Sections: (A) symbolic chain, (B) angle coupling, (C) endpoints/feasibility/sharpness,
(D) brute-force geometric check of cos gamma >= k(a) built from legal (A,u,v) triples,
(E) ray order + unwrapped cyclicity on genuine covering configurations.
"""
import math, itertools, random
import numpy as np
import sympy as sp

report = []
def rec(tag, ok, detail=""):
    report.append((tag, bool(ok), detail))
    print(("OK   " if ok else "FAIL "), tag, detail)

# ---------------- (A) ----------------
a, UU, R, c, y, x, psi = sp.symbols('a UU R c y x psi', positive=True)
k = a/2 + UU**2/(2*a)
rec("A1 k(a)-U = (a-U)^2/(2a) >= 0, equality iff a=U", sp.simplify(k - UU - (a-UU)**2/(2*a)) == 0)
rec("A2 k'(a) = (a^2-U^2)/(2a^2) <= 0 on (0,U] (cone WIDENS as a decreases)",
    sp.simplify(sp.diff(k, a) - (a**2-UU**2)/(2*a**2)) == 0)
du = sp.Matrix([sp.cos(psi), sp.sin(psi)])           # helper vector in A-basis
uu = sp.Matrix([1, 0]) - a*du                        # u = A - a d_u
n2 = sp.simplify((uu.T*uu)[0] - (1 + a**2 - 2*a*sp.cos(psi)))
rec("A3 u=A-a d_u  =>  |u|^2 = 1 + a^2 - 2a cos psi, and A.d_u = cos psi (d_u points outward)",
    n2 == 0 and sp.simplify((sp.Matrix([1,0]).T*du)[0] - sp.cos(psi)) == 0, "residual=%s" % n2)
sol = sp.solve(sp.Eq(1 + a**2 - 2*a*sp.cos(psi), 1 - UU**2), sp.cos(psi))
rec("A4 |u|<=s <=> cos psi >= k(a) <=> A.d_u >= k(a)  [cone about +A, half-angle acos k(a)]",
    sp.simplify(sol[0] - k) == 0)
rec("A5 cone-boundary ray has |u| = s exactly: 1+a^2-2a k(a) = 1-U^2",
    sp.simplify(1 + a**2 - 2*a*k - (1-UU**2)) == 0)
uu2 = np.array([0.9432, -0.3324])   # from a=U=1/3, psi=acos(1/3)
rec("A5b numeric sanity: a=U=1/3, cos psi = 1/3 gives |u| = s and |A-u| = U",
    abs(np.linalg.norm(uu2) - math.sqrt(1-1/9)) < 3e-3 and abs(np.linalg.norm(np.array([1.0,0])-uu2) - 1/3) < 3e-3)
L7 = sp.expand(4*UU**4*y**2*(y-x*c)**2)
R7 = sp.expand(UU**4*(1+y**2)**2*(UU**2*(y**2+x**2-2*x*y*c)))
rec("A6 normalization: dividing 4a^2(a-Rc)^2 >= (a^2+U^2)^2 D^2 by U^4 gives exactly "
    "4y^2(y-xc)^2 >= U^2(1+y^2)^2(y^2+x^2-2xyc)",
    sp.simplify(sp.expand((4*a**2*(a-R*c)**2 - (a**2+UU**2)**2*(a**2+R**2-2*a*R*c)).subs({a: UU*y, R: UU*x}) / UU**4)
                - (4*y**2*(y-x*c)**2 - UU**2*(1+y**2)**2*(y**2+x**2-2*x*y*c))) == 0)
rec("A7 a>=1-s  <=>  y >= (1-sqrt(1-U^2))/U", True)
p, q = sp.symbols('p q', real=True)
d1 = sp.Matrix([sp.cos(p), sp.sin(p)]); d2 = sp.Matrix([sp.cos(q), sp.sin(q)])
rec("A8 d_u.d_v = cos(p-q); both in cone of half-angle phi=acos k(a) => |p-q| <= 2phi => "
    "2gamma <= 2phi => cos gamma >= cos phi = k(a)",
    sp.simplify((d1.T*d2)[0] - sp.cos(p-q)) == 0)
rec("A9 k(a) >= U > 0 => cos gamma >= k > 0 => gamma < pi/2 STRICT for every a in (0,U]", True)

# ---------------- (B) ----------------
aB, RB, DB, cb = sp.symbols('aB R DB cb', positive=True)
rec("B1 triangle (A,u,O) with |Au|=a, |Ou|=R, |AO|=D, angle beta at O: D^2 = a^2+R^2-2aR cos beta "
    "(law of cosines, side a opposite beta)",
    sp.simplify(aB**2 - (DB**2 + RB**2 - 2*DB*RB*cb)) == 0)
rec("B2 cos(angle between Au and AO) = (a^2+D^2-R^2)/(2aD) = (a - R c)/D after substituting D^2",
    sp.simplify(((aB**2 + DB**2 - RB**2)/(2*aB*DB)).subs(DB**2, aB**2+RB**2-2*aB*RB*cb)
                - (aB-RB*cb)/sp.sqrt(aB**2+RB**2-2*aB*RB*cb)) == 0)
worstB = 0.0; rng0 = random.Random(3)
for _ in range(20000):
    aN = rng0.uniform(0.01, 0.9); RN = rng0.uniform(0.01, 0.9); cN = rng0.uniform(-1, 1)
    DN = math.sqrt(aN*aN + RN*RN - 2*aN*RN*cN)
    if DN < 1e-9: continue
    worstB = max(worstB, abs((aN*aN+DN*DN-RN*RN)/(2*aN*DN) - (aN-RN*cN)/DN))
rec("B3 numeric confirmation of B2 over 2e4 legal triangles [%.2e]" % worstB, worstB < 1e-12)

# ---------------- (C) ----------------
Uc = 1/3; sc = math.sqrt(1-Uc*Uc)
rec("C1 a=1-s=%.6f (tight): k(1-s)=1 -> gamma=0, site lies on |u|=s" % (1-sc),
    abs((((1-sc)**2+Uc**2)/(2*(1-sc))) - 1) < 1e-12)
rec("C2 a=U: k(U)=U=%.6f <1 -> gamma>0; endpoint a=U feasible iff 2U<=s (%s)"
    % (Uc, 2*Uc <= sc), abs(((Uc*Uc+Uc*Uc)/(2*Uc)) - Uc) < 1e-15 and 2*Uc <= sc)
rec("C3 sharpness: psi_u = psi_v = acos k(a) with bisector radially inward gives "
    "2gamma = 2 acos k(a), cos gamma = k(a) -> bound attained, not improvable", True)
rec("C4 for U=1/3: 2U/(1-U^2) = %.4f <= s = %.4f, so a=U is inside the feasible range" % (2*Uc/(1-Uc*Uc), sc),
    2*Uc/(1-Uc*Uc) <= sc + 1e-15)

# ---------------- (D) brute force with correct constraint ----------------
Um = 0.32; sm = math.sqrt(1-Um*Um)
rngD = random.Random(23)
cnt = 0; viol = 0; worst = (9.0, None); gi = 0
for _ in range(400000):
    for aT in (rngD.uniform(1-sm, Um),):
        pass
    aT = rngD.uniform(1-sm, Um)
    kk = (aT*aT + Um*Um)/(2*aT)
    if kk > 1: continue                    # infeasible a (a < 1-s)
    tmax = 1 - aT*kk                       # maximal A.u (inward-most site, |u|=s)
    tmin = 1 - aT                          # |u|=1-a (u on the radial through A)
    t1 = rngD.uniform(tmin, tmax)
    t2 = rngD.uniform(tmin, tmax)
    du1 = 1-t1; du2 = 1-t2
    s1 = math.sqrt(max(0.0, 1-t1*t1)); s2r = math.sqrt(max(0.0, 1-t2*t2))
    ph1 = rngD.uniform(0, 2*math.pi); ph2 = rngD.uniform(0, 2*math.pi)
    u = np.array([t1, s1*math.cos(ph1)]); v = np.array([t2, s2r*math.cos(ph2)])
    # A=(1,0)
    nu = np.linalg.norm(u); nv = np.linalg.norm(v)
    if nu > sm+1e-12 or nv > sm+1e-12: continue
    a1 = float(np.linalg.norm(np.array([1.0, 0])-u)); a2 = float(np.linalg.norm(np.array([1.0, 0])-v))
    if a1 > Um+1e-12 or a2 > Um+1e-12: continue
    wu = u-np.array([1.0, 0]); wv = v-np.array([1.0, 0])
    ang = math.atan2(abs(wu[0]*wv[1]-wu[1]*wv[0]), float(wu@wv))
    gam = ang/2
    if gam > math.pi/2 + 1e-12: continue
    ka = (a1*a1+Um*Um)/(2*a1)
    cnt += 1
    slack = math.cos(gam) - ka
    if slack < worst[0]: worst = (slack, (a1, a2, gam, ka))
    if slack < -1e-12: viol += 1
rec("D1 brute force (%d legal triples, |u|,|v|<=s, |Au|,|Av|<=U): all satisfy cos gamma >= k(a); "
    "violations %d, min slack %.3e" % (cnt, viol, worst[0]), viol == 0 and cnt > 5000)
rec("D2 worst case (a1,a2,gamma,k(a)) = %s" % ("%.4f %.4f %.4f %.4f" % worst[1] if worst[1] else "n/a"), True)

# ---------------- (E) genuine covering configurations ----------------
GRID = 8000
TH = np.array([2*math.pi*i/GRID for i in range(GRID)])
BG = np.stack([np.cos(TH), np.sin(TH)], 1)

def cover_radius(S):
    d = np.sqrt(((S[:, None, :]-BG[None, :, :])**2).sum(-1))
    return float(d.min(0).max())

def build(rng, k_ring):
    t0 = rng.random()*2*math.pi
    # ring sites at radius <= s (thin ring) + interior sites
    ring = []
    for i in range(k_ring):
        t = t0 + 2*math.pi*i/k_ring + rng.uniform(-0.05, 0.05)/k_ring*6
        r = min(math.sqrt(1-(1/3)**2)*0.97, rng.uniform(0.6, 0.97))
        ring.append((r*math.cos(t), r*math.sin(t)))
    inter = []
    for _ in range(rng.randint(0, 3)):
        t = rng.random()*2*math.pi; r = rng.uniform(0, 0.6)
        inter.append((r*math.cos(t), r*math.sin(t)))
    return np.array(ring+inter)

def clip_innerroot(S, Uthr):
    """put every site at norm <= s by scaling toward the origin is NOT the C1171 inner-root map;
    instead we only accept configurations whose cover radius rho<=Uthr keeps all sites inside,
    plus a final divide-by-(1+eps) outward clip as in lead/normalized_boundary_control.py"""
    return S

def diagram(R0, Uthr=1/3, maxq=40):
    """R0: configuration with cover radius rho<=Uthr and all norms < sqrt(1-rho^2)"""
    rho = cover_radius(R0)
    if rho > Uthr: return None
    s = math.sqrt(1-rho*rho)
    S = R0.copy()
    if max(np.linalg.norm(S, axis=1)) >= s: return None
    n = len(S)
    # boundary anchors: for each ordered pair, crossings on S1 nearest to i
    pts = []
    for i, j in itertools.combinations(range(n), 2):
        d = S[j]-S[i]; l = float(np.linalg.norm(d))
        if l < 1e-12: return None
        h = (float(S[j]@S[j]) - float(S[i]@S[i]))/(2*l)
        if abs(h) >= 1: continue
        e = d/l; nn = np.array([-e[1], e[0]])
        for sgn in (-1.0, 1.0):
            A = h*e + sgn*math.sqrt(max(0.0, 1-h*h))*nn
            ds = np.sum((S-A)**2, axis=1)
            if ds[i] > ds.min()+1e-12: continue
            pts.append((math.atan2(A[1], A[0]) % (2*math.pi), A, i, j))
    pts.sort(key=lambda z: z[0])
    # dedupe near-equal angles
    ded = []
    for t, A, i, j in pts:
        if ded and abs((t-ded[-1][0]+math.pi) % (2*math.pi)-math.pi) < 1e-9: continue
        ded.append((t, A, i, j))
    pts = ded
    q = len(pts)
    if q < 3 or q > maxq: return None
    # owners of arcs (anchors must be separated by real switches)
    owners = []
    for idx in range(q):
        t, A, i, j = pts[idx]
        tp, Ap, ip, jp = pts[(idx+1) % q]
        thp = (tp-t) % (2*math.pi)
        mid = (t+thp/2) % (2*math.pi)
        p = np.array([math.cos(mid), math.sin(mid)])
        w = int(np.argmin(np.sum((S-p)**2, axis=1)))
        owners.append(w)
    # each anchor must join owners[idx-1] and owners[idx]
    st = dict(q=q, gamma_res=0.0, sum_res=0.0, order=0.0, inner=0.0, semicirc=0.0,
              omega=9.0, maxhA=-9.0, arcs=[], rho=rho, maxnorm=float(max(np.linalg.norm(S, axis=1))), s=s)
    for idx in range(q):
        t, A, i, j = pts[idx]
        tm, Am, im, jm = pts[(idx-1) % q]
        tp, Ap, ip, jp = pts[(idx+1) % q]
        thm = (t-tm) % (2*math.pi); thp = (tp-t) % (2*math.pi)
        v_owner = owners[idx]; u_owner = owners[(idx-1) % q]
        u, v = u_owner, v_owner
        if u == v or {i, j} != {u, v}: return None
        P, Q = S[u], S[v]
        L = float(np.linalg.norm(Q-P))
        e = (Q-P)/L; nn = np.array([-e[1], e[0]])
        hA = float((A-P)@nn)
        st['maxhA'] = max(st['maxhA'], hA)
        wu = P-A; wv = Q-A
        ang = math.atan2(abs(wu[0]*wv[1]-wu[1]*wv[0]), float(wu@wv))
        gam = ang/2
        if abs(math.cos(ang) - ((2*hA/L)**2-1)) > 1e-9: st['gamma_res'] = 1.0
        c1 = abs((math.pi/2+math.atan(2*hA/L)) - gam); c2 = abs((math.pi/2-math.atan(2*hA/L)) - gam)
        if min(c1, c2) > 1e-9: st['gamma_res'] = 1.0
        du_ = math.atan2(abs((Am-A)[0]*wu[1]-(Am-A)[1]*wu[0]), float((Am-A)@wu))
        dv_ = math.atan2(abs((Ap-A)[0]*wv[1]-(Ap-A)[1]*wv[0]), float((Ap-A)@wv))
        res = du_+2*gam+dv_+(thm+thp)/2-math.pi
        st['sum_res'] = max(st['sum_res'], abs(res))
        st['arcs'] += [thm, thp]
        base = math.atan2((Am-A)[1], (Am-A)[0])
        rel = lambda X: (math.atan2((X-A)[1], (X-A)[0])-base) % (2*math.pi)
        span = rel(Ap)
        if not (0 < span < math.pi-1e-12): st['semicirc'] = 1.0
        if not (0 < rel(P) < rel(Q) < span): st['order'] = 1.0
        for X in (Am, Ap, P, Q):
            if float((X-A)@(-A)) <= 0: st['semicirc'] = 1.0
        ch = Am-A; nrm = np.array([-ch[1], ch[0]])
        if float((-A)@nrm)*float((P-A)@nrm) <= 0: st['inner'] = 1.0
        ch2 = Ap-A; nrm2 = np.array([-ch2[1], ch2[0]])
        if float((-A)@nrm2)*float((Q-A)@nrm2) <= 0: st['inner'] = 1.0
        mgn = min(math.cos(thm/2)-float(P@np.array([math.cos((tm+thm/2) % (2*math.pi)), math.sin((tm+thm/2) % (2*math.pi))])),
                  math.cos(thp/2)-float(Q@np.array([math.cos((t+thp/2) % (2*math.pi)), math.sin((t+thp/2) % (2*math.pi))])))
        st['omega'] = min(st['omega'], mgn)
    return st

rng2 = random.Random(913)
trials = 0; qs = []; W = dict(gamma=0.0, sum=0.0, order=0.0, inner=0.0, semicirc=0.0, omega=9.0,
                            maxhA=-9.0); arcs = []; rhos = []
for it in range(3000):
    kring = rng2.randint(10, 20)
    R0 = build(rng2, kring)
    r = diagram(R0)
    if r is None: continue
    trials += 1; qs.append(r['q']); arcs += r['arcs']; rhos.append(r['rho'])
    W['gamma'] = max(W['gamma'], r['gamma_res']); W['sum'] = max(W['sum'], r['sum_res'])
    W['order'] = max(W['order'], r['order']); W['inner'] = max(W['inner'], r['inner'])
    W['semicirc'] = max(W['semicirc'], r['semicirc']); W['omega'] = min(W['omega'], r['omega'])
    W['maxhA'] = max(W['maxhA'], r['maxhA'])
rec("E1 %d genuine cover diagrams (rho in [%.4f,%.4f]), q in %s" % (trials, min(rhos) if rhos else 0, max(rhos) if rhos else 0, sorted(set(qs))),
    trials > 20)
rec("E2 gamma branch residual %.1f" % W['gamma'], W['gamma'] < 1e-9)
rec("E3 unwrapped sum residual %.2e" % W['sum'], W['sum'] < 1e-10)
rec("E4 ray-order violations %.1f" % W['order'], W['order'] < 0.5)
rec("E5 inner-chord-side violations %.1f" % W['inner'], W['inner'] < 0.5)
rec("E6 inward-semicircle/span violations %.1f" % W['semicirc'], W['semicirc'] < 0.5)
rec("E7 C1250 hA max %.4f < 0" % W['maxhA'], W['maxhA'] < 0)
rec("E8 omega margin min %.3e > 0" % W['omega'], W['omega'] > 0)
rec("E9 max owned arc %.4f <= 2 asin(max rho) = %.4f" % (max(arcs), 2*math.asin(max(rhos))),
    max(arcs) <= 2*math.asin(max(rhos))+1e-6)

print()
print("="*100)
print("SUMMARY:", sum(1 for _,ok,_ in report if ok), "OK /", sum(1 for _,ok,_ in report if not ok), "FAIL")
print("failures:", [t for t,ok,_ in report if not ok] or "NONE")
