"""root-cc2 innernorm-envelope: resolve the branches and give the explicit formula.

Coordinates: x_pm = (H, +-v), H = cos h, v = sin h; c = (H-d, b), d > 0, b >= 0.
    cot alpha = (d^2 + b^2 - v^2)/(2 d v).
Legal region:  d^2 + (b-v)^2 <= r^2,  d^2 + (b+v)^2 <= r^2,  d^2 + b^2 <= 2Hd + v^2 - r^2.

Objective: MINIMISE alpha in [0,pi], i.e. MINIMISE the angle (NOT cot: cot changes sign).
This script computes alpha at the candidate points and compares, and scans the legal set
for the true minimum alpha.
"""
import sys
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
mp.mp.dps = 40
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

U = mp.mpf('0.33173203427623414'); r = U
S = mp.sqrt(1 - r*r); HMAX = mp.asin(r)

def alpha_of(d, b, v):
    """angle at c = (H-d, b) subtended by x_pm; computed via the two vectors."""
    # vectors u = x_+ - c = (d, v - b), w = x_- - c = (d, -v - b)
    u = (d, v - b); w = (d, -v - b)
    nu = mp.sqrt(u[0]**2 + u[1]**2); nw = mp.sqrt(w[0]**2 + w[1]**2)
    if nu == 0 or nw == 0: return mp.mpf(0)
    cs = (u[0]*w[0] + u[1]*w[1])/(nu*nw)
    cs = max(mp.mpf(-1), min(mp.mpf(1), cs))
    return mp.acos(cs)

P('=' * 78)
P('r = %s ; s = %s ; h_max = asin r = %s' % (mp.nstr(r, 12), mp.nstr(S, 12), mp.nstr(HMAX, 12)))
P('')
P('(1) min over the legal set (grid) vs the candidate formulas')
P('    h      theta    min_alpha(grid)  argmin(d,b)      both-tight pi/2-h   E2(norm)  E3(one+norm)')
for hv in ['0.05', '0.10', '0.166', '0.20', '0.25', '0.30', '0.338']:
    h = mp.mpf(hv)
    if h > HMAX: P('    %s beyond h_max' % hv); continue
    H = mp.cos(h); v = mp.sin(h)
    dmax = mp.sqrt(max(mp.mpf(0), r*r - v*v))
    best = None
    N = 600
    for i in range(0, N+1):
        d = dmax*mp.mpf(i)/N
        sw = mp.sqrt(max(mp.mpf(0), r*r - d*d))
        bhi = v + sw
        blo = max(mp.mpf(0), v - sw)
        Q = 2*H*d + v*v - r*r
        bN = mp.sqrt(Q - d*d) if Q - d*d > 0 else mp.mpf(0)
        bm = min(bhi, bN)
        if bm < blo: continue
        for j in range(0, 101):
            b = blo + (bm - blo)*mp.mpf(j)/100
            a = alpha_of(d, b, v)
            if best is None or a < best[0]:
                best = (a, d, b)
    amin, d1, b1 = best if best else (None, None, None)
    # both-tight point: b=0, d=sqrt(r^2-v^2)
    dE1 = dmax; aE1 = alpha_of(dE1, mp.mpf(0), v)
    # E2 inner norm with b=0: (H-d)^2 = s^2 -> d = H-s
    dE2 = H - S
    aE2 = alpha_of(dE2, mp.mpf(0), v) if dE2 > 0 else None
    # E3 one endpoint tight + inner norm
    def eq(d):
        bb = (H*d - r*r + v*v)/v
        return d*d + (bb+v)**2 - r*r
    aE3 = None
    if eq(mp.mpf('1e-12'))*eq(dE1) < 0:
        lo, hi = mp.mpf('1e-12'), dE1
        for _ in range(300):
            mid = (lo+hi)/2
            if eq(lo)*eq(mid) <= 0: hi = mid
            else: lo = mid
        d3 = (lo+hi)/2; b3 = (H*d3 - r*r + v*v)/v
        if b3 >= 0: aE3 = alpha_of(d3, b3, v)
    P('    %-6s %-8s %-16s (%.6f,%.6f) %-18s %-10s %-10s'
      % (hv, mp.nstr(2*h, 6), mp.nstr(amin, 10), float(d1), float(b1),
         mp.nstr(mp.pi/2 - h, 10), mp.nstr(aE2, 8) if aE2 is not None else 'n/a',
         mp.nstr(aE3, 8) if aE3 is not None else 'n/a'))
    P('           both-tight alpha = %s (check == pi/2-h: %s) ; grid argmin matches both-tight: %s'
      % (mp.nstr(aE1, 10), mp.nstr(aE1-(mp.pi/2-h), 3),
         mp.nstr(abs(d1-dE1), 3) + '/' + mp.nstr(abs(b1), 3)))

P('')
P('=' * 78)
P('(2) the both-tight identity: at b=0, d=sqrt(r^2-v^2) the three points c,x+,x- lie on')
P('    a circle of radius r through x_pm, so the inscribed-angle theorem gives alpha = pi/2 - h')
P('    (half the arc that the chord x+x- cuts off on that circle is pi/2 - h when the centre')
P('    lies outside the unit disk... verified numerically above).')
P('')
P('(3) the inner-norm constraint in these coordinates: |c| <= s <=> d^2+b^2 <= 2Hd+v^2-r^2')
P('    Is the both-tight point legal?  |c| = H - sqrt(r^2-v^2) ; check numerically:')
for hv in ['0.05', '0.10', '0.20', '0.30', '0.338']:
    h = mp.mpf(hv)
    if h > HMAX: continue
    H = mp.cos(h); v = mp.sin(h)
    dE1 = mp.sqrt(r*r - v*v)
    cn = H - dE1
    P('    h=%-6s |c|=%s  s=%s  legal: %s ; v vs r/2: %s'
      % (hv, mp.nstr(cn, 10), mp.nstr(S, 8), cn <= S, mp.nstr(v, 6) + ' vs ' + mp.nstr(r/2, 6)))

(OUT / 'explore04.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'explore04.txt')
