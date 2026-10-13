"""STRICT legal-cover probe for the ray-order premises of BOUNDARY-CYCLICITY-PROOF.md.

A configuration is called STRICT LEGAL when
  (i)   rho := true covering radius of the site set for the closed unit disk satisfies rho <= 1/3;
  (ii)  every site has norm < sqrt(1-rho^2)            [C1171 norm cap, self-consistent rho];
  (iii) every owned boundary arc has length <= 2 asin(rho)   [owner arc cap].
For each genuine boundary switch we then read off:
  hA sign, the ray order A_- < u < bisector < v < A_+, all four rays in the inward semicircle,
  owner strictly on the inner side of its chord, and the unwrapped closure residual
  delta_u + 2 gamma_A + delta_v + (theta_u+theta_v)/2 - pi.
"""
import math, itertools, random
import numpy as np

U = 1/3.0
GRID = 12000
TH = np.array([2*math.pi*i/GRID for i in range(GRID)])
BG = np.stack([np.cos(TH), np.sin(TH)], 1)

def cover_radius(S):
    d = np.sqrt(((S[:, None, :]-BG[None, :, :])**2).sum(-1))
    return float(d.min(0).max())

def build(rng, k_ring):
    t0 = rng.random()*2*math.pi
    pts = []
    for i in range(k_ring):
        t = t0 + 2*math.pi*i/k_ring + rng.uniform(-0.2, 0.2)/k_ring*3
        r = rng.uniform(0.62, 0.98)*math.sqrt(1-U*U)
        pts.append((r*math.cos(t), r*math.sin(t)))
    for _ in range(rng.randint(0, 4)):
        t = rng.random()*2*math.pi; r = rng.uniform(0, 0.7)*math.sqrt(1-U*U)
        pts.append((r*math.cos(t), r*math.sin(t)))
    return np.array(pts)

def diagram(R0):
    S = R0.copy(); n = len(S)
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
    ded = []
    for t, A, i, j in pts:
        if ded and abs((t-ded[-1][0]+math.pi) % (2*math.pi)-math.pi) < 1e-9: continue
        ded.append((t, A, i, j))
    pts = ded; q = len(pts)
    if q < 4: return None
    st = dict(q=q, sum_res=0.0, order=0.0, inner=0.0, semicirc=0.0, omega=9.0, maxhA=-9.0, arcs=[])
    for idx in range(q):
        t, A, i, j = pts[idx]
        tm, Am = pts[(idx-1) % q][0], pts[(idx-1) % q][1]
        tp, Ap = pts[(idx+1) % q][0], pts[(idx+1) % q][1]
        thm = (t-tm) % (2*math.pi); thp = (tp-t) % (2*math.pi)
        ta = (tm+thm/2) % (2*math.pi); tb = (t+thp/2) % (2*math.pi)
        pm = np.array([math.cos(ta), math.sin(ta)]); pp = np.array([math.cos(tb), math.sin(tb)])
        u = int(np.argmin(np.sum((S-pm)**2, axis=1)))
        v = int(np.argmin(np.sum((S-pp)**2, axis=1)))
        if u == v or {u, v} != {i, j}: return None
        P, Q = S[u], S[v]
        L = float(np.linalg.norm(Q-P))
        e = (Q-P)/L; nn = np.array([-e[1], e[0]])
        hA = float((A-P)@nn)
        st['maxhA'] = max(st['maxhA'], hA)
        wu = P-A; wv = Q-A
        gam = math.atan2(abs(wu[0]*wv[1]-wu[1]*wv[0]), float(wu@wv))/2
        du_ = math.atan2(abs((Am-A)[0]*wu[1]-(Am-A)[1]*wu[0]), float((Am-A)@wu))
        dv_ = math.atan2(abs((Ap-A)[0]*wv[1]-(Ap-A)[1]*wv[0]), float((Ap-A)@wv))
        st['sum_res'] = max(st['sum_res'], abs(du_+2*gam+dv_+(thm+thp)/2-math.pi))
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
        mgn = min(math.cos(thm/2)-float(P@pm), math.cos(thp/2)-float(Q@pp))
        st['omega'] = min(st['omega'], mgn)
    return st

rng = random.Random(4242)
trials = 0; qs = []; arcs = []; rhos = []
W = dict(sum=0.0, order=0.0, inner=0.0, semicirc=0.0, omega=9.0, maxhA=-9.0)
for it in range(8000):
    S = build(rng, rng.randint(9, 18))
    rho = cover_radius(S)
    if rho > U: continue
    if max(np.linalg.norm(S, axis=1)) >= math.sqrt(1-rho*rho): continue
    d = diagram(S)
    if d is None: continue
    if max(d['arcs']) > 2*math.asin(min(1.0, rho))+1e-9: continue
    trials += 1; qs.append(d['q']); arcs += d['arcs']; rhos.append(rho)
    for kk in ('sum', 'order', 'inner', 'semicirc'):
        W[kk] = max(W[kk], d[kk+'_res'] if kk == 'sum' else d[kk])
    W['omega'] = min(W['omega'], d['omega']); W['maxhA'] = max(W['maxhA'], d['maxhA'])
print("STRICT LEGAL covers found: %d   q in %s" % (trials, sorted(set(qs))))
print("rho in [%.4f, %.4f]  (U=1/3)" % (min(rhos), max(rhos)))
print("max ||site|| < sqrt(1-rho^2) enforced per configuration")
print("unwrapped closure residual  = %.3e" % W['sum'])
print("ray-order violations        = %.1f" % W['order'])
print("inner-chord-side violations = %.1f" % W['inner'])
print("semicircle violations       = %.1f" % W['semicirc'])
print("max owned arc = %.4f <= 2 asin(max rho) = %.4f" % (max(arcs), 2*math.asin(max(rhos))))
print("all hA < 0 ?  max hA = %.4f" % W['maxhA'])
print("omega margin min = %.3e" % W['omega'])
