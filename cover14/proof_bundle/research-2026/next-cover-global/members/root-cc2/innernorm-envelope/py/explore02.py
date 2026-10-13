"""root-cc2 innernorm-envelope: exploration with the CORRECT feasible region.

Endpoints x_pm = (cos h, +-sin h), h = theta/2.  A center is legal iff |c - x_pm| <= r,
|c| <= s = sqrt(1-r^2), and c is on the origin's side of the chord x = cos h.
The lens {|c-x_pm| <= r} is nonempty iff sin h <= r; the chord midpoint is legal, so the
region is never empty for sin h <= r.

We want the MINIMUM viewing angle alpha (max of sin(alpha/2)) over the legal region.
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
S = mp.sqrt(1 - r*r)
HMAX = mp.asin(r)
P('=' * 78)
P('U = r = %s ; s = sqrt(1-r^2) = %s ; h_max = asin(r) = %s ; theta_max = 2h_max = %s'
  % (mp.nstr(r, 14), mp.nstr(S, 14), mp.nstr(HMAX, 12), mp.nstr(2*HMAX, 12)))
P('')
P('structural consequences:')
P('  * lens midpoint (cos h, 0): |c| = cos h <= s  <=>  cos^2 h <= 1-r^2  <=>  sin h >= r,')
P('    so for sin h < r the INNER NORM BINDS; for sin h >= r the chord itself is inside B(0,s).')
P('  * the lens exists only for sin h <= r, so the legal nonempty range is sin h <= r,')
P('    i.e. theta <= 2 asin r = L (the cap).')
P('  * farthest-from-origin point of the lens: corner (cos h - sqrt(r^2-sin^2 h), 0);')
P('    |corner| = cos h - sqrt(r^2 - sin^2 h) < cos h < s -> the inner norm does NOT bind')
P('    at the corners either.  => the inner norm NEVER binds.  Hypothesis then falsifies the')
P('    "one endpoint radius r plus |c|=s" branch as an extremiser.')

def alpha_at(h, c):
    xp = (mp.cos(h), mp.sin(h)); xm = (mp.cos(h), -mp.sin(h))
    a = mp.sqrt((c[0]-xp[0])**2 + (c[1]-xp[1])**2)
    b = mp.sqrt((c[0]-xm[0])**2 + (c[1]-xm[1])**2)
    area = abs((xp[0]-c[0])*(xm[1]-c[1]) - (xp[1]-c[1])*(xm[0]-c[0]))/2
    if area == 0: return mp.mpf(0), a, b
    d = 2*mp.sin(h)
    R = a*b*d/(4*area)
    return d/(2*R), a, b

P('')
P('=' * 78)
P('(1) max of sin(alpha/2) over the legal region (grid, then refine)')
P('    h       theta      maxsin(grid)   argmax c          |c|      a        b')
for hv in ['0.05', '0.10', '0.20', '0.30', '0.337']:
    h = mp.mpf(hv)
    if h > HMAX: P('    %-7s beyond h_max' % hv); continue
    best = None
    # parameterise the lens: for each x in [cos h - sqrt(r^2-sin^2h), cos h], y range
    w = mp.sqrt(r*r - mp.sin(h)**2)
    N = 400
    for i in range(N+1):
        x = mp.cos(h) - w + w*mp.mpf(i)/N
        if x <= 0: continue
        half = mp.sqrt(max(mp.mpf(0), r*r - (x-mp.cos(h))**2))
        M = 400
        for j in range(M+1):
            y = -half + 2*half*mp.mpf(j)/M
            c = (x, y)
            if c[0]**2 + c[1]**2 > S*S + mp.mpf('1e-30'): continue
            v, a, b = alpha_at(h, c)
            if best is None or v > best[0]:
                best = (v, c, a, b)
    v, c, a, b = best
    P('    %-7s %-10s %-14s (%s,%s) %-8s %-8s %s'
      % (hv, mp.nstr(2*h, 8), mp.nstr(v, 10), mp.nstr(c[0], 6), mp.nstr(c[1], 6),
         mp.nstr(mp.sqrt(c[0]**2+c[1]**2), 6), mp.nstr(a, 8), mp.nstr(b, 8)))
    P('            alpha = 2 asin(.) = %s ; equal radii a=b=r? %s ; |c|=s? %s'
      % (mp.nstr(2*mp.asin(v), 10), mp.nstr(a-r, 3) + '/' + mp.nstr(b-r, 3),
         mp.nstr(mp.sqrt(c[0]**2+c[1]**2)-S, 3)))

P('')
P('=' * 78)
P('(2) candidate family: equal endpoint radii a = b = r (c on the perpendicular bisector')
P('    at distance sqrt(r^2 - sin^2 h) from the chord midpoint)')
P('    h       sin(alpha/2)   alpha        |c|        |c|<=s?')
for hv in ['0.05', '0.10', '0.20', '0.30', '0.337']:
    h = mp.mpf(hv)
    if h > HMAX: continue
    t = mp.sqrt(r*r - mp.sin(h)**2)
    c = (mp.cos(h) - t, mp.mpf(0))
    v, a, b = alpha_at(h, c)
    P('    %-7s %-14s %-12s %-10s %s'
      % (hv, mp.nstr(v, 10), mp.nstr(2*mp.asin(v), 10), mp.nstr(abs(c[0]), 8),
         'yes' if abs(c[0]) <= S else 'NO'))
P('')
P('    geometric identity for a=b=r: the chord x_+x_- is seen from the centre of the')
P('    circle through x_+,x_-,c, so alpha = pi - theta  (check numerically):')
for hv in ['0.05', '0.10', '0.20', '0.30']:
    h = mp.mpf(hv)
    t = mp.sqrt(r*r - mp.sin(h)**2)
    c = (mp.cos(h) - t, mp.mpf(0))
    v, a, b = alpha_at(h, c)
    P('      h=%-6s 2 asin(v)=%s  pi-2h=%s  diff=%s'
      % (hv, mp.nstr(2*mp.asin(v), 10), mp.nstr(mp.pi-2*h, 10), mp.nstr(2*mp.asin(v)-(mp.pi-2*h), 6)))

(OUT / 'explore02.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'explore02.txt')
