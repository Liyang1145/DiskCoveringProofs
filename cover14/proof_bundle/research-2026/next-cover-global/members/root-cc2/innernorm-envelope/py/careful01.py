"""root-cc2 innernorm-envelope: careful recomputation of alpha at candidate points.

For x_pm = (H, +-v), c = (H-d, b):
    u = x_+ - c = (d, v-b),  w = x_- - c = (d, -v-b)
    |u x w| = 2 d v          (cross product, exact)
    u . w   = d^2 - (v^2 - b^2) = d^2 + b^2 - v^2
    alpha = atan2(2 d v, d^2 + b^2 - v^2)   in (0, pi)
Constraints: d^2 + (b-v)^2 <= r^2, d^2 + (b+v)^2 <= r^2, d^2 + b^2 <= 2Hd + v^2 - r^2.
"""
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)
mp.mp.dps = 50
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

r = mp.mpf('0.33173203427623414'); S = mp.sqrt(1-r*r)

def alpha(d, b, H, v):
    num = 2*d*v; den = d*d + b*b - v*v
    return mp.atan2(num, den)

def legal(d, b, H, v):
    e1 = d*d + (b-v)**2 <= r*r + mp.mpf('1e-30')
    e2 = d*d + (b+v)**2 <= r*r + mp.mpf('1e-30')
    nn = d*d + b*b <= 2*H*d + v*v - r*r + mp.mpf('1e-30')
    return e1 and e2 and nn

P('=' * 78)
P('(0) sanity: alpha at the chord midpoint c=(H,0) (d=0,b=0)')
for hv in ['0.05', '0.20']:
    h = mp.mpf(hv); H = mp.cos(h); v = mp.sin(h)
    P('    h=%s alpha(d=0,b=0) = %s (should be pi)' % (hv, mp.nstr(alpha(mp.mpf('1e-12'), mp.mpf(0), H, v), 10)))

P('')
P('(1) the E1 point: b=0, d=sqrt(r^2-v^2) (both endpoint distances = r)')
for hv in ['0.05', '0.10', '0.20', '0.30']:
    h = mp.mpf(hv); H = mp.cos(h); v = mp.sin(h)
    d = mp.sqrt(r*r - v*v); b = mp.mpf(0)
    a = alpha(d, b, H, v)
    a1 = mp.sqrt(d*d + (b-v)**2); a2 = mp.sqrt(d*d + (b+v)**2)
    cn = mp.sqrt((H-d)**2 + b*b)
    P('    h=%-6s d=%-12s a=%s  |u|=%-12s |w|=%-12s |c|=%-12s legal=%s'
      % (hv, mp.nstr(d, 8), mp.nstr(a, 10), mp.nstr(a1, 10), mp.nstr(a2, 10), mp.nstr(cn, 10),
         legal(d, b, H, v)))
    P('            pi/2-h = %s ; pi-2h = %s ; 2h = %s' % (mp.nstr(mp.pi/2-h, 10), mp.nstr(mp.pi-2*h, 10), mp.nstr(2*h, 10)))

P('')
P('(2) fine 2D minimisation of alpha over the legal set (correct bounds)')
P('    h      theta    min alpha        (d,b)                  |c|        a_+        a_-      endpoints tight?')
for hv in ['0.05', '0.10', '0.166', '0.20', '0.25', '0.30', '0.335']:
    h = mp.mpf(hv); H = mp.cos(h); v = mp.sin(h)
    dmax = mp.sqrt(max(mp.mpf(0), r*r - v*v))
    best = None
    N = 1200
    for i in range(0, N+1):
        d = dmax*mp.mpf(i)/N
        w = mp.sqrt(max(mp.mpf(0), r*r - d*d))
        blo = max(mp.mpf(0), v - w); bhi = w - v
        if bhi < blo: continue
        Q = 2*H*d + v*v - r*r
        bN = mp.sqrt(Q - d*d) if Q - d*d > 0 else mp.mpf(0)
        bm = min(bhi, bN)
        if bm < blo: continue
        for j in range(0, 401):
            b = blo + (bm - blo)*mp.mpf(j)/400
            a = alpha(d, b, H, v)
            if best is None or a < best[0]:
                best = (a, d, b)
    a, d, b = best
    a1 = mp.sqrt(d*d + (b-v)**2); a2 = mp.sqrt(d*d + (b+v)**2)
    cn = mp.sqrt((H-d)**2 + b*b)
    P('    %-6s %-8s %-16s (%.6f, %.6f)  %-10s %-10s %-10s %s/%s'
      % (hv, mp.nstr(2*h, 6), mp.nstr(a, 12), float(d), float(b), mp.nstr(cn, 10),
         mp.nstr(a1, 10), mp.nstr(a2, 10), mp.nstr(a1-r, 3), mp.nstr(a2-r, 3)))
    P('           pi/2-h = %s ; alpha-(pi/2-h) = %s' % (mp.nstr(mp.pi/2-h, 12), mp.nstr(a-(mp.pi/2-h), 8)))

(OUT / 'careful01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'careful01.txt')
