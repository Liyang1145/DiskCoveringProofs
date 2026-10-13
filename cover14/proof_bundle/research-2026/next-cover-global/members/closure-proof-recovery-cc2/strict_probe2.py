"""FINAL strict probe, with the two extra OWNSHIP conditions that the phantom-switch
degeneracy requires (and that OWNER-COUNT-UNIFICATION provides analytically):

  (O1) the arc between consecutive anchors A_k, A_{k+1} has a single owner, verified at
       several interior sample points (no phantom switches: no site is nearest at an
       isolated boundary point only);
  (O2) the owner of the arc (A_{k-1},A_k) and of (A_k,A_{k+1}) are exactly the two sites
       nearest at A_k, and both differ.

Then, with (i) rho<=1/3, (ii) all ||site|| < sqrt(1-rho^2), (iii) all owned arcs <= 2 asin rho,
we read off the ray-order premises and the unwrapped closure residual.
"""
import math, itertools, random
import numpy as np

U = 1/3.0
GRID = 16000
TH = np.array([2*math.pi*i/GRID for i in range(GRID)])
BG = np.stack([np.cos(TH), np.sin(TH)], 1)

def cover_radius(S):
    d = np.sqrt(((S[:, None, :]-BG[None, :, :])**2).sum(-1))
    return float(d.min(0).max())

def build(rng, k_ring):
    t0 = rng.random()*2*math.pi
    pts = []
    for i in range(k_ring):
        t = t0 + 2*math.pi*i/k_ring + rng.uniform(-0.25, 0.25)/k_ring*3
        r = rng.uniform(0.72, 0.995)*math.sqrt(1-U*U)
        pts.append((r*math.cos(t), r*math.sin(t)))
    for _ in range(rng.randint(0, 4)):
        t = rng.random()*2*math.pi; r = rng.uniform(0, 0.75)*math.sqrt(1-U*U)
        pts.append((r*math.cos(t), r*math.sin(t)))
    return np.array(pts)

def owner(S, ang):
    p = np.array([math.cos(ang), math.sin(ang)])
    return int(np.argmin(np.sum((S-p)**2, axis=1)))

def probe(S, rho, verbose=False):
    n = len(S)
    # candidate anchors
    pts = []
    for i, j in itertools.combinations(range(n), 2):
        dv = S[j]-S[i]; l = float(np.linalg.norm(dv))
        if l < 1e-12: return None
        h = (float(S[j]@S[j]) - float(S[i]@S[i]))/(2*l)
        if abs(h) >= 1: continue
        e = dv/l; nn = np.array([-e[1], e[0]])
        for sgn in (-1.0, 1.0):
            A = h*e + sgn*math.sqrt(max(0.0, 1-h*h))*nn
            ds = np.sum((S-A)**2, axis=1)
            if ds[i] > ds.min()+1e-13: continue
            pts.append((math.atan2(A[1], A[0]) % (2*math.pi), A, i, j))
    if not pts: return None
    pts.sort(key=lambda z: z[0])
    ded = []
    for t, A, i, j in pts:
        if ded and abs((t-ded[-1][0]+math.pi) % (2*math.pi)-math.pi) < 1e-8: continue
        ded.append((t, A, i, j))
    pts = ded; q = len(pts)
    if q < 5: return None
    # (O1) single owner per arc, sampled at 5 interior points
    arcmid_owner = []
    for idx in range(q):
        t = pts[idx][0]; tp = pts[(idx+1) % q][0]
        thp = (tp-t) % (2*math.pi)
        if thp < 1e-6: return None
        ows = set()
        for f in (0.15, 0.35, 0.5, 0.65, 0.85):
            ows.add(owner(S, (t+f*thp) % (2*math.pi)))
        if len(ows) != 1: return None            # multiple/phiantom switches inside
        arcmid_owner.append(ows.pop())
    st = dict(q=q, sum_res=0.0, order=0.0, inner=0.0, semicirc=0.0, omega=9.0, maxhA=-9.0, arcs=[])
    for idx in range(q):
        t, A, i, j = pts[idx]
        tm, Am = pts[(idx-1) % q][0], pts[(idx-1) % q][1]
        tp, Ap = pts[(idx+1) % q][0], pts[(idx+1) % q][1]
        thm = (t-tm) % (2*math.pi); thp = (tp-t) % (2*math.pi)
        u = arcmid_owner[(idx-1) % q]; v = arcmid_owner[idx]
        # (O2) the two owners must be the two nearest sites at A
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
        if not (0 < span < math.pi+1e-12): st['semicirc'] = 1.0
        if not (0 < rel(P) < rel(Q) < span): st['order'] = 1.0
        for X in (Am, Ap, P, Q):
            if float((X-A)@(-A)) <= 0: st['semicirc'] = 1.0
        ch = Am-A; nrm = np.array([-ch[1], ch[0]])
        if float((-A)@nrm)*float((P-A)@nrm) <= 0: st['inner'] = 1.0
        ch2 = Ap-A; nrm2 = np.array([-ch2[1], ch2[0]])
        if float((-A)@nrm2)*float((Q-A)@nrm2) <= 0: st['inner'] = 1.0
        pm = np.array([math.cos((tm+thm/2) % (2*math.pi)), math.sin((tm+thm/2) % (2*math.pi))])
        pp = np.array([math.cos((t+thp/2) % (2*math.pi)), math.sin((t+thp/2) % (2*math.pi))])
        mgn = min(math.cos(thm/2)-float(P@pm), math.cos(thp/2)-float(Q@pp))
        st['omega'] = min(st['omega'], mgn)
    return st

rng = random.Random(99887)
trials = 0; qs = []; arcs = []; rhos = []
W = dict(sum=0.0, order=0.0, inner=0.0, semicirc=0.0, omega=9.0, maxhA=-9.0)
for it in range(20000):
    S = build(rng, rng.randint(10, 20))
    rho = cover_radius(S)
    if rho > U: continue
    if max(np.linalg.norm(S, axis=1)) >= math.sqrt(1-rho*rho): continue
    d = probe(S, rho)
    if d is None: continue
    if max(d['arcs']) > 2*math.asin(min(1.0, rho))+1e-9: continue
    trials += 1; qs.append(d['q']); arcs += d['arcs']; rhos.append(rho)
    for kk in ('sum', 'order', 'inner', 'semicirc'):
        W[kk] = max(W[kk], d[kk+'_res'] if kk == 'sum' else d[kk])
    W['omega'] = min(W['omega'], d['omega']); W['maxhA'] = max(W['maxhA'], d['maxhA'])
print("STRICT LEGAL covers (O1,O2 ownership + rho<=1/3 + normcap + arc cap): %d" % trials)
if trials:
    print("q in %s ; rho in [%.4f, %.4f] ; max owned arc %.4f <= 2 asin(max rho) = %.4f"
          % (sorted(set(qs)), min(rhos), max(rhos), max(arcs), 2*math.asin(max(rhos))))
    print("unwrapped closure residual  = %.3e" % W['sum'])
    print("ray-order violations        = %.1f" % W['order'])
    print("inner-chord-side violations = %.1f" % W['inner'])
    print("semicircle violations       = %.1f" % W['semicirc'])
    print("omega margin min            = %.3e" % W['omega'])
    print("all hA < 0 ? max hA         = %.4f" % W['maxhA'])
