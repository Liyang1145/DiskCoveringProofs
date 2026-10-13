"""root-cc2 innernorm-envelope: CORRECT alpha and the resolved classification.

alpha in (0,pi); with x_pm = (H,+-v), c = (H-d,b):
    cot alpha = (d^2 + b^2 - v^2)/(2 d v)   (exact; |u x w| = 2 d v, u.w = d^2+b^2-v^2)
so alpha = acot(cot) with the convention acot(0) = pi/2, acot(-inf) = pi.
(The earlier atan2-based expression was wrong in the branch; that is fixed here.)
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
HM = mp.asin(r)

def cot_of(d, b, v):
    return (d*d + b*b - v*v)/(2*d*v) if d > 0 else mp.inf

def alpha(d, b, v):
    if d <= 0: return mp.pi
    c = cot_of(d, b, v)
    if c >= 0: return mp.atan(1/c) if c > 0 else mp.pi/2
    return mp.pi + mp.atan(1/c)          # atan(1/c) < 0 here

# cross-check alpha against the direct dot/cross computation
def alpha_direct(d, b, v):
    u = (d, v-b); w = (d, -v-b)
    nu = mp.sqrt(u[0]**2+u[1]**2); nw = mp.sqrt(w[0]**2+w[1]**2)
    cs = (u[0]*w[0]+u[1]*w[1])/(nu*nw)
    return mp.acos(max(mp.mpf(-1), min(mp.mpf(1), cs)))

P('=' * 78)
P('(0) cross-check of alpha: acot formula vs direct arccos')
for hv in ['0.05', '0.10', '0.20', '0.30']:
    h = mp.mpf(hv); H = mp.cos(h); v = mp.sin(h)
    for (d, b) in [(mp.sqrt(r*r-v*v), mp.mpf(0)), (mp.mpf('0.1'), mp.mpf('0.2'))]:
        P('    h=%-6s d=%-10s b=%-8s acot=%s direct=%s diff=%s'
          % (hv, mp.nstr(d, 6), mp.nstr(b, 5), mp.nstr(alpha(d, b, v), 10),
             mp.nstr(alpha_direct(d, b, v), 10), mp.nstr(alpha(d, b, v)-alpha_direct(d, b, v), 3)))

P('')
P('=' * 78)
P('(1) the E1 point (b=0, d=sqrt(r^2-v^2)): alpha and its exact closed form')
for hv in ['0.05', '0.10', '0.20', '0.30', '0.335']:
    h = mp.mpf(hv); v = mp.sin(h)
    d = mp.sqrt(r*r - v*v)
    P('    h=%-6s alpha=%-14s pi-2h=%-14s  2h=%-12s  cot=(r^2-2v^2)/(2v sqrt(r^2-v^2))=%s'
      % (hv, mp.nstr(alpha(d, mp.mpf(0), v), 12), mp.nstr(mp.pi-2*h, 12), mp.nstr(2*h, 10),
         mp.nstr((r*r-2*v*v)/(2*v*d), 10)))

P('')
P('=' * 78)
P('(2) fine minimisation over the legal set')
P('    h      theta    min alpha        (d,b)                  a_+        a_-        a_=r? a_-=r? |c|=s?')
for hv in ['0.05', '0.10', '0.166', '0.20', '0.25', '0.30', '0.335']:
    h = mp.mpf(hv); H = mp.cos(h); v = mp.sin(h)
    dmax = mp.sqrt(max(mp.mpf(0), r*r - v*v))
    best = None
    N = 1000
    for i in range(1, N+1):
        d = dmax*mp.mpf(i)/N
        w = mp.sqrt(max(mp.mpf(0), r*r - d*d))
        blo = max(mp.mpf(0), v - w); bhi = w - v
        if bhi < blo: continue
        Q = 2*H*d + v*v - r*r
        bN = mp.sqrt(Q - d*d) if Q - d*d > 0 else mp.mpf(0)
        bm = min(bhi, bN)
        if bm < blo: continue
        for j in range(0, 301):
            b = blo + (bm - blo)*mp.mpf(j)/300
            a = alpha(d, b, v)
            if best is None or a < best[0]:
                a1 = mp.sqrt(d*d + (b-v)**2); a2 = mp.sqrt(d*d + (b+v)**2)
                cn = mp.sqrt((H-d)**2 + b*b)
                best = (a, d, b, a1, a2, cn)
    a, d, b, a1, a2, cn = best
    P('    %-6s %-8s %-16s (%.6f, %.6f)  %-10s %-10s %-5s %-6s %s'
      % (hv, mp.nstr(2*h, 6), mp.nstr(a, 12), float(d), float(b), mp.nstr(a1, 10),
         mp.nstr(a2, 10), mp.nstr(a1-r, 3), mp.nstr(a2-r, 3), mp.nstr(cn-S, 3)))
    P('           pi-2h = %s ; min alpha - (pi-2h) = %s ; E1 alpha = %s'
      % (mp.nstr(mp.pi-2*h, 12), mp.nstr(a-(mp.pi-2*h), 8),
         mp.nstr(alpha(dmax, mp.mpf(0), v), 12)))

(OUT / 'careful02.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'careful02.txt')
