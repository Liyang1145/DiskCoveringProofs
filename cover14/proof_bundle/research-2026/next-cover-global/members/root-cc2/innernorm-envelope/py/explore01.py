"""root-cc2 innernorm-envelope: exploratory numerics for the sharper envelope.

Setup. Endpoints x_pm = (cos h, +-sin h) on the unit circle, h = theta/2 in (0,pi/2].
A center c is legal if |c - x_pm| <= r (covers both endpoints) and |c| <= s = sqrt(1-r^2)
(inner norm).  We minimise the viewing angle alpha(c) = angle(x_+ - c, x_- - c) over the
legal region, i.e. maximise sin(alpha/2) = |x_+ - x_-| / (2 R(c)) where R(c) is the
circumradius of (c, x_+, x_-).

Also reports the two candidate extremisers:
  E1 equal endpoint radii: |c - x_+| = |c - x_-| and (if it binds) |c| = s;
  E2 one endpoint at distance r and |c| = s.
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

U = mp.mpf('0.33173203427623414')
Rr = U
S = mp.sqrt(1 - Rr*Rr)

def sinhalf(h, c):
    xp = (mp.cos(h), mp.sin(h)); xm = (mp.cos(h), -mp.sin(h))
    d = mp.sqrt((xp[0]-xm[0])**2 + (xp[1]-xm[1])**2)     # = 2 sin h
    a = mp.sqrt((c[0]-xp[0])**2 + (c[1]-xp[1])**2)
    b = mp.sqrt((c[0]-xm[0])**2 + (c[1]-xm[1])**2)
    # circumradius R = a b d / (4 Area); use the triangle area via the cross product
    area = abs((xp[0]-c[0])*(xm[1]-c[1]) - (xp[1]-c[1])*(xm[0]-c[0]))/2
    R = a*b*d/(4*area) if area > 0 else mp.inf
    return d/(2*R) if R != mp.inf else mp.mpf(0), a, b, R

P('=' * 78)
P('U = %s ; s = sqrt(1-U^2) = %s' % (mp.nstr(U, 12), mp.nstr(S, 12)))
P('')
P('(1) legal region and the minimum of sin(alpha/2) over it, by 2D grid + local refine')
P('    h      sin(alpha/2)_max(grid)   argmax c      |c|      a=|c-x+|  b=|c-x-|')
for hv in ['0.40', '0.50', '0.60', '0.70', '0.80', '0.90', '1.00', '1.10', '1.20', '1.40']:
    h = mp.mpf(hv)
    if mp.sin(h) > Rr:
        P('    %-6s INFEASIBLE (sin h = %s > r = %s)' % (hv, mp.nstr(mp.sin(h), 6), mp.nstr(Rr, 6)))
        continue
    best = None
    N = 260
    for i in range(N+1):
        for j in range(N+1):
            cx = -S + 2*S*mp.mpf(i)/N
            for jj in range(N+1):
                yy = -S + 2*S*mp.mpf(jj)/N
                pass
    # use polar sampling around the origin for efficiency
    N = 400
    for i in range(N+1):
        rad = S*mp.mpf(i)/N
        M = max(3, int(8 + 700*rad/S))
        for j in range(M):
            th = 2*mp.pi*mp.mpf(j)/M
            c = (rad*mp.cos(th), rad*mp.sin(th))
            d1 = mp.sqrt((c[0]-mp.cos(h))**2 + (c[1]-mp.sin(h))**2)
            d2 = mp.sqrt((c[0]-mp.cos(h))**2 + (c[1]+mp.sin(h))**2)
            if d1 <= Rr and d2 <= Rr:
                v = sinhalf(h, c)[0]
                if best is None or v > best[0]:
                    best = (v, c, d1, d2)
    if best is None:
        P('    %-6s no legal point found on the grid' % hv)
        continue
    v, c, d1, d2 = best
    P('    %-6s %-20s (%s,%s) %s  %s %s'
      % (hv, mp.nstr(v, 12), mp.nstr(c[0], 6), mp.nstr(c[1], 6), mp.nstr(mp.sqrt(c[0]**2+c[1]**2), 8),
         mp.nstr(d1, 8), mp.nstr(d2, 8)))
    P('           theta = 2h = %s ; arc angle alpha = 2 asin(.) = %s'
      % (mp.nstr(2*h, 8), mp.nstr(2*mp.asin(v), 10)))

P('')
P('=' * 78)
P('(2) candidate E1: |c - x+| = |c - x-| = r  (equal endpoint radii, unconstrained by |c|<=s)')
P('    then the centre is at distance sqrt(r^2 - sin^2 h) beyond the chord midpoint, so')
P('    alpha = pi - theta (half of alpha is pi/2 - h) ; |c|^2 = cos^2 h - sin^2 h + r^2 - sin^2 h')
P('    h      alpha_E1=pi-2h   |c|_E1   |c|<=s ?')
for hv in ['0.40', '0.60', '0.80', '1.00', '1.20', '1.40']:
    h = mp.mpf(hv)
    if mp.sin(h) > Rr:
        P('    %-6s (-)  no equal-radius centre with a=b=r' % hv); continue
    cn = mp.sqrt(Rr*Rr - mp.sin(h)**2) + mp.cos(h)
    P('    %-6s %-14s %-10s %s' % (hv, mp.nstr(mp.pi - 2*h, 10), mp.nstr(cn, 8),
                                  'yes' if cn <= S else 'NO (inner norm binds)'))

P('')
P('=' * 78)
P('(3) candidate E2: |c - x+| = r and |c| = s')
P('    c = t (cos h, sin h) + sqrt(r^2 - t^2) (-sin h, cos h) with |c| = s; solve for t')
for hv in ['0.40', '0.60', '0.80', '1.00', '1.20']:
    h = mp.mpf(hv)
    if mp.sin(h) > Rr:
        P('    %-6s infeasible' % hv); continue
    # |c|^2 = t^2 + (r^2 - t^2) = r^2 if the offset is perpendicular -> |c| = r always!
    # but the offset direction is (-sin h, cos h); |c|^2 = t^2 + r^2 - t^2 + 2 t sqrt(r^2-t^2) (x.(-sin,cos))
    # x = (cos h, sin h); x . (-sin h, cos h) = 0, so |c|^2 = t^2 + (r^2 - t^2) = r^2.
    P('    %-6s |c| = r = %s for EVERY point at distance r from x+?! (x . perp = 0)' % (hv, mp.nstr(Rr, 8)))
    # verify numerically
    t = mp.mpf('0.15')
    c = (t*mp.cos(h) - mp.sqrt(Rr*Rr-t*t)*mp.sin(h), t*mp.sin(h) + mp.sqrt(Rr*Rr-t*t)*mp.cos(h))
    P('           check: t=0.15 -> c=(%s,%s) |c|=%s' % (mp.nstr(c[0], 8), mp.nstr(c[1], 8),
                                                       mp.nstr(mp.sqrt(c[0]**2+c[1]**2), 10)))

(OUT / 'explore01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'explore01.txt')
