"""Independent audit kernel for lead/CORE-TWO-HUB-DOMAIN.md.

Claim set (file CORE-TWO-HUB-DOMAIN.md):
  a = 1-2r, core = closed disc B(0,a).
  (C1) 9 ring discs (|a_j| >= 1-r) miss open B(0,a); so in a cover the 2 hubs cover B(0,a).
  (C2) Branch A: s_j <= r-a  => hub j alone covers the core.
  (C3) Branch B: neither alone => beta_j = acos((a^2+s_j^2-r^2)/(2 a s_j)) in (0,pi) and
        core circle covered by the two arcs   <=>   beta_1+beta_2 >= 2pi-delta.
  (C4) hence beta_1+beta_2 >= pi, equivalently (s1+s2)(s1 s2 + a^2 - r^2) <= 0,
        equivalently s1 s2 <= r^2 - a^2; so min(s1,s2) <= sqrt(r^2-a^2).
  (C5) r >= 1/3 necessary (for r<a two radius-r discs cannot cover the core).
  (C6) r = 19/50: sqrt(r^2-a^2) = sqrt(217)/50 ~ .294618.

This kernel checks (C3) by a DIFFERENT representation (direct dense sampling of the
core circle against the union of the two closed discs -- no arc algebra), checks the
algebra of (C4) symbolically, checks (C2),(C5),(C6) and gives the sharpness example.
"""
import numpy as np, sympy as sp

rng = np.random.default_rng(20260924)
r = 0.38
a = 1 - 2*r
print("r=%.4f  a=1-2r=%.4f  r-a=%.4f  sqrt(r^2-a^2)=%.10f  1-r=%.4f" %
      (r, a, r-a, np.sqrt(r*r-a*a), 1-r))
print("exact at r=19/50: r^2-a^2 =", sp.Rational(19,50)**2 - sp.Rational(1-2*sp.Rational(19,50))**2,
      " sqrt =", sp.sqrt(sp.Rational(217,2500)), "=", float(sp.sqrt(sp.Rational(217,2500))))

# ---------- (C3): direct geometric test of "two arcs cover the core circle" ----------
def core_circle_covered(s1, s2, delta, r, a, n=200000):
    """direct: is every point of circle radius a around origin within r of h1 or h2?"""
    h1 = np.array([s1, 0.0])
    h2 = s2*np.array([np.cos(delta), np.sin(delta)])
    t = np.linspace(0, 2*np.pi, n, endpoint=False)
    P = a*np.stack([np.cos(t), np.sin(t)], 1)
    d1 = np.sqrt(((P-h1)**2).sum(1)); d2 = np.sqrt(((P-h2)**2).sum(1))
    return bool(np.all(np.minimum(d1, d2) <= r))

def beta(s, r, a):
    return np.arccos((a*a + s*s - r*r)/(2*a*s))

NT = 0; NW = []
for _ in range(300):
    s1 = 10**rng.uniform(np.log10(r-a+1e-9), np.log10(r+a-1e-9)) if r > a else 0
    s1 = float(np.clip(s1, r-a+1e-9, r+a-1e-9))
    s2 = float(rng.uniform(r-a+1e-9, r+a-1e-9))
    delta = float(rng.uniform(0, np.pi))
    pred = (beta(s1, r, a) + beta(s2, r, a)) >= 2*np.pi - delta - 1e-12
    real = core_circle_covered(s1, s2, delta, r, a)
    NT += 1
    if pred != real:
        NW.append((s1, s2, delta, pred, real,
                   beta(s1,r,a)+beta(s2,r,a), 2*np.pi-delta))
print("\n(C3) arc criterion vs direct dense sampling: %d random cases, %d mismatches" % (NT, len(NW)))
for w in NW[:6]:
    print("   s1=%.6f s2=%.6f d=%.6f pred=%s real=%s bsum=%.6f 2pi-d=%.6f" % w)

# boundary stress: cases exactly at the threshold
print("\n(C3) tangential stress (bsum = 2pi-delta exactly):")
for (s1, s2) in [(r-a+1e-6, r-a+1e-6), (np.sqrt(r*r-a*a), np.sqrt(r*r-a*a)), (0.29, 0.31)]:
    b1, b2 = beta(s1, r, a), beta(s2, r, a)
    dcrit = 2*np.pi - (b1+b2)
    if 0 <= dcrit <= np.pi:
        for eps in (-1e-4, 0, 1e-4):
            d = dcrit + eps
            if 0 <= d <= np.pi:
                print("   s=(%.6f,%.6f) delta=%.6f(+%.0e): criteria %s / direct %s" %
                      (s1, s2, d, eps, (b1+b2) >= 2*np.pi-d-1e-12,
                       core_circle_covered(s1, s2, d, r, a, n=400000)))

# ---------- (C4): algebra, symbolically ----------
s1, s2, A, R = sp.symbols('s1 s2 A R', positive=True)
C1 = (A**2 + s1**2 - R**2)/(2*A*s1)
C2 = (A**2 + s2**2 - R**2)/(2*A*s2)
expr = sp.simplify(C1 + C2)
prod = sp.simplify(2*A*s1*s2*expr)
fac = sp.factor(sp.expand(prod))
print("\n(C4) 2*a*s1*s2*(C1+C2) factors as:", fac)
target = sp.expand((s1+s2)*(s1*s2 + A**2 - R**2))
print("     equals (s1+s2)(s1 s2 + a^2 - r^2)?", sp.simplify(fac - target) == 0)

# ---------- (C2) Branch A ----------
print("\n(C2) Branch A: if s_j <= r-a then B(0,a) subset B(h_j,r):")
for rr in (0.34, 0.38, 0.45, 0.49):
    aa = 1-2*rr
    if aa <= 0: continue
    s = rr-aa
    worst = s + aa        # max |x-h| over |x|<=a  <=  s+a
    print("   r=%.2f a=%.4f s=r-a=%.4f  max_{|x|<=a}|x-h| = s+a = %.10f <= r=%s" %
          (rr, aa, s, worst, worst <= rr + 1e-15))

# ---------- (C5) ----------
print("\n(C5) max half-width of the core-circle arc of one radius-r disc (core radius a):")
for rr in (0.30, 0.32, 0.333, 0.34, 0.40, 0.49):
    aa = 1-2*rr
    if aa <= 0: continue
    if aa > rr:                       # r < 1/3: g(s) is minimised at s=sqrt(a^2-r^2), smax>=0
        smin = np.sqrt(aa*aa-rr*rr)
        bmax = beta(smin, rr, aa)
    else:                             # r >= 1/3: g increasing on [r-a, r+a] -> beta max at s=r-a
        smin = rr-aa
        bmax = beta(smin + 1e-12, rr, aa) if smin > 1e-9 else np.pi
    print("   r=%.4f a=%.4f: admissible s in [%.4f,%.4f], bmax=%.6f rad (pi/2=%.6f) ; "
          "two discs can cover core? %s" %
          (rr, aa, max(0.0, rr-aa), rr+aa, bmax, np.pi/2, 2*bmax >= np.pi - 1e-12))

# ---------- sharpness ----------
print("\n(C6) sharpness: s1=s2=sqrt(r^2-a^2), delta=pi (r=19/50):")
rq = 19/50; aq = 1-2*rq; sq = np.sqrt(rq*rq-aq*aq)
b = beta(sq, rq, aq)
print("   s=%.10f beta=%.10f (pi/2=%.10f) beta1+beta2=%.10f >= 2pi-delta=pi : %s" %
      (sq, b, np.pi/2, 2*b, 2*b >= np.pi - 1e-12))
print("   direct core circle cover (delta=pi):", core_circle_covered(sq, sq, np.pi, rq, aq, n=400000))

# ---------- certified object consistency ----------
import io, json
d = json.load(io.open('n11/upper/certified_object.json', encoding='utf-8'))
C = np.array([[int(x)/1e17, int(y)/1e17] for x, y in d['centers_scaled_1e17']])
rho = np.hypot(C[:,0], C[:,1]); H2 = C[rho < 0.62]
s = np.hypot(H2[:,0], H2[:,1]); delta = float(np.arccos(np.clip(H2[0]@H2[1]/(s[0]*s[1]), -1, 1)))
rr = 0.3799838531198387090; aa = 1-2*rr
print("\ncertified object hubs: s=(%.6f, %.6f) delta=%.6f" % (s[0], s[1], delta))
print("   r-a=%.4f  sqrt(r^2-a^2)=%.6f  min s=%.6f <= bound? %s" %
      (rr-aa, np.sqrt(rr*rr-aa*aa), s.min(), s.min() <= np.sqrt(rr*rr-aa*aa)))
print("   beta sum = %.6f ; 2pi-delta = %.6f ; criterion holds? %s" %
      (beta(s[0],rr,aa)+beta(s[1],rr,aa), 2*np.pi-delta,
       beta(s[0],rr,aa)+beta(s[1],rr,aa) >= 2*np.pi-delta))
print("   direct core-circle check:", core_circle_covered(s[0], s[1], delta, rr, aa, n=400000))
print("   is s[0] <= r-a (=C450 .14 domain)?", s[0] <= rr-aa)
