"""root-cc2 innernorm-envelope: reconcile the grid minimum with the L1 formula.

For h = theta/2 fixed at 0.1 (theta = 0.2), find the exact minimiser of alpha over the
legal set by a fresh fine scan, print its full data, and compare with the L1 formula.
"""
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)
mp.mp.dps = 50
log = []
def P(*a):
    x = ' '.join(str(z) for z in a); print(x); log.append(x)

r = mp.mpf('0.33173203427623414'); s = mp.sqrt(1-r*r)
th = mp.mpf('0.2'); h = th/2
H = mp.cos(h); v = mp.sin(h)
P('theta = %s ; h = %s ; H = %s ; v = %s' % (th, h, mp.nstr(H, 14), mp.nstr(v, 14)))

def alpha_from(d, b):
    cot = (d*d + b*b - v*v)/(2*d*v)
    if cot > 0: return mp.atan(1/cot)
    if cot == 0: return mp.pi/2
    return mp.pi + mp.atan(1/cot)

def data(d, b):
    a1 = mp.sqrt(d*d + (b-v)**2); a2 = mp.sqrt(d*d + (b+v)**2)
    cn = mp.sqrt((H-d)**2 + b*b)
    return a1, a2, cn

P('')
P('(1) very fine scan over the legal set')
best = None
NA, NB = 4000, 2000
dmax = mp.sqrt(r*r - v*v)
P('    dmax = sqrt(r^2-v^2) = %s' % mp.nstr(dmax, 12))
for i in range(1, NA+1):
    d = dmax*mp.mpf(i)/NA
    w = mp.sqrt(max(mp.mpf(0), r*r - d*d))
    blo = max(mp.mpf(0), v - w); bhi = w - v
    if bhi < blo: continue
    Q = 2*H*d + v*v - r*r
    bN = mp.sqrt(Q - d*d) if Q - d*d > 0 else mp.mpf(0)
    bm = min(bhi, bN)
    if bm < blo: continue
    for j in range(0, NB+1):
        b = blo + (bm - blo)*mp.mpf(j)/NB
        a = alpha_from(d, b)
        if best is None or a < best[0]:
            best = (a, d, b)
a, d, b = best
a1, a2, cn = data(d, b)
P('    best alpha = %s at (d,b) = (%s, %s)' % (mp.nstr(a, 12), mp.nstr(d, 14), mp.nstr(b, 14)))
P('    endpoint distances: a_+ = %s ; a_- = %s  (r = %s)' % (mp.nstr(a1, 12), mp.nstr(a2, 12), mp.nstr(r, 12)))
P('    |c| = %s (s = %s) ; |c|-s = %s' % (mp.nstr(cn, 12), mp.nstr(s, 12), mp.nstr(cn-s, 8)))
P('    norms: a_+ - r = %s ; a_- - r = %s ; d^2+(b-v)^2 - r^2 = %s ; d^2+b^2-(2Hd+v^2-r^2) = %s'
  % (mp.nstr(a1-r, 8), mp.nstr(a2-r, 8), mp.nstr(d*d+(b-v)**2-r*r, 8),
     mp.nstr(d*d+b*b-(2*H*d+v*v-r*r), 8)))

P('')
P('(2) the L1-formula inversion for theta = 0.2')
s_ = s
L1 = lambda x: x - mp.acos(s_*mp.cos(x)) + mp.asin(r)
lo, hi = mp.mpf('1e-12'), mp.mpf('0.92')
for _ in range(300):
    m = (lo+hi)/2
    if L1(m) < th: lo = m
    else: hi = m
aL1 = (lo+hi)/2
P('    alpha from L1(alpha) = theta: %s ; alpha from the scan: %s ; diff = %s'
  % (mp.nstr(aL1, 12), mp.nstr(a, 12), mp.nstr(aL1-a, 8)))
P('')
P('(3) at the formula point, what are the actual distances?  Set alpha = aL1, |c| = s,')
P('    and solve for the configuration with the two endpoints on the unit circle; then')
P('    check whether BOTH endpoint distances can be <= r (needed for a legal cover).')
al = aL1
c = (s, mp.mpf(0))                      # rotate so c is on the x-axis
# unit points x with the angle at c between them equal to al: they lie on a line at
# distance ... solve parametrically: x = c + t (cos mu, sin mu), |x| = 1
# for each direction mu, t solves t^2 + 2 t (c.dir)t + |c|^2 - 1 = 0.
# The angle at c between the two rays is al, so the rays are at mu and mu + al with
# t's adjusted; both endpoints must have |x| = 1.
# Solve: for ray direction (cos mu, sin mu), t(mu) = -c.cos(mu) + sqrt((c.cos mu)^2 - |c|^2 + 1)
def ray_end(mu):
    cd = c[0]*mp.cos(mu) + c[1]*mp.sin(mu)
    disc = cd*cd - (c[0]**2+c[1]**2) + 1
    if disc < 0: return None
    t = -cd + mp.sqrt(disc)
    return (c[0] + t*mp.cos(mu), c[1] + t*mp.sin(mu)), t
# find mu such that the angle between the two endpoints (as seen from c) equals al and
# at least one endpoint is at distance r (t = r)
# t = r means cd = (|c|^2 + r^2 - 1)/(2 ... ) let us solve: t=r -> disc = (r + cd)^2
# -> cd^2 - |c|^2 + 1 = r^2 + 2 r cd + cd^2 -> -|c|^2 + 1 = r^2 + 2 r cd
# -> cd = (1 - |c|^2 - r^2)/(2r) = (1 - (1-r^2) - r^2)/(2r) = 0
P('    t = r requires c.(cos mu, sin mu) = (1 - |c|^2 - r^2)/(2r) = %s'
  % mp.nstr((1 - (s*s) - r*r)/(2*r), 12))
P('    so the endpoint at distance r has ray direction perpendicular to c (cd = 0),')
P('    i.e. mu = +-pi/2, and then t = sqrt(1 - |c|^2) = r (consistent).')
for sgn in (1, -1):
    mu = sgn*mp.pi/2
    e, t = ray_end(mu)
    u = (e[0]-c[0], e[1]-c[1])
    P('    endpoint direction mu=%+s: point = (%s,%s), |point| = %s, t = %s'
      % (sgn, mp.nstr(e[0], 12), mp.nstr(e[1], 12),
         mp.nstr(mp.sqrt(e[0]**2+e[1]**2), 12), mp.nstr(t, 12)))

(OUT / 'reconcile01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'reconcile01.txt')
