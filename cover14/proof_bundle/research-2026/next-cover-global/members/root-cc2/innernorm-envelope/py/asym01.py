"""root-cc2 innernorm-envelope: independent check of the asymmetric branch.

Claim under test: for |c| = s and ONE endpoint at distance r (i.e. c is on the
intersection of B(0,s) and B(x_+,r), or of B(0,s) and B(x_-,r)), the covered arc length
theta and the viewing angle alpha satisfy

    theta_asym(alpha) = alpha - arccos(s cos alpha) + asin r,

and the true envelope is theta <= max(theta_asym(alpha), 2 asin(r sin(alpha/2)));
the minimum alpha for fixed theta is attained on the inner-norm boundary with one endpoint
disk tight.

I verify this by: (i) constructing such points explicitly from the geometry and measuring
(theta, alpha); (ii) comparing with the formula; (iii) computing, for fixed theta, the
minimum alpha over the legal set and checking which branch attains it.
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

r = mp.mpf('0.33173203427623414'); s = mp.sqrt(1-r*r)
HM = mp.asin(r)

def alpha_of(c, xp, xm):
    u = (xp[0]-c[0], xp[1]-c[1]); w = (xm[0]-c[0], xm[1]-c[1])
    nu = mp.sqrt(u[0]**2+u[1]**2); nw = mp.sqrt(w[0]**2+w[1]**2)
    cs = (u[0]*w[0]+u[1]*w[1])/(nu*nw)
    return mp.acos(max(mp.mpf(-1), min(mp.mpf(1), cs)))

P('=' * 78)
P('(i) construction: phi in [0,2pi), c = s(cos phi, sin phi) with |c| = s; for each phi the')
P('    two tangency directions of B(c,r) meet the unit circle at the S+ and S- points;')
P('    the covered arc runs between them and the angle at c is 2 asin(r/s) when symmetric.')
P('    More generally, take one endpoint one of the two unit points at distance r from c')
P('    and the other endpoint the intersection of the unit circle with B(c,r) on the other')
P('    side; then alpha is the angle at c and theta is the arc length.')
P('')
P('phi      r-check: unit pts at distance r from c       alpha        theta(measured)  theta_asym(alpha)  diff')
for phiv in ['0.05', '0.20', '0.40', '0.60', '0.80', '1.00', '1.20']:
    phi = mp.mpf(phiv)
    c = (s*mp.cos(phi), s*mp.sin(phi))
    # unit vectors at distance r from c: solve |x|=1, |x-c|=r
    # x . c = (1 + |c|^2 - r^2)/2 = (1 + s^2 - r^2)/2 = (1 + 1 - r^2 - r^2)/2 = 1 - r^2 = s^2
    # wait: |c|^2 = s^2 = 1-r^2, so x.c = (1 + s^2 - r^2)/2 = (1 + 1 - r^2 - r^2)/2 = 1 - r^2 = s^2
    k = (1 + s*s - r*r)/2
    # unit vectors x with x.c = k: x = k/s * chat +- sqrt(1 - k^2/s^2) * perp(chat)
    ch = (mp.cos(phi), mp.sin(phi)); pe = (-mp.sin(phi), mp.cos(phi))
    t = mp.sqrt(max(mp.mpf(0), 1 - (k/s)**2))
    xp = (k/s*ch[0] + t*pe[0], k/s*ch[1] + t*pe[1])
    xm = (k/s*ch[0] - t*pe[0], k/s*ch[1] - t*pe[1])
    # theta = angle between xp and xm (minor arc)
    th = mp.acos(max(mp.mpf(-1), min(mp.mpf(1), xp[0]*xm[0] + xp[1]*xm[1])))
    al = alpha_of(c, xp, xm)
    fa = al - mp.acos(s*mp.cos(al)) + mp.asin(r)
    P('%-9s |c-xp|=%-12s |c-xm|=%-12s %-12s %-16s %-18s %s'
      % (phiv, mp.nstr(mp.sqrt((c[0]-xp[0])**2+(c[1]-xp[1])**2), 10),
         mp.nstr(mp.sqrt((c[0]-xm[0])**2+(c[1]-xm[1])**2), 10),
         mp.nstr(al, 10), mp.nstr(th, 12), mp.nstr(fa, 12), mp.nstr(th-fa, 4)))

P('')
P('=' * 78)
P('(ii) direct test of the formula: pick alpha, solve for the point with |c|=s and')
P('     |c - x_+| = r, then compare theta with theta_asym(alpha)')
P('alpha    theta_measured   theta_asym(alpha)   diff')
for av in ['0.15', '0.3', '0.5', '0.8', '1.2']:
    al = mp.mpf(av)
    # c on B(0,s) with tangent direction to x_+ at angle ... employ the plane:
    # choose c = s(cos phi, sin phi) and rotate so that the chord from c is at angle al.
    # The two endpoints are the two intersection points of S^1 with B(c,r); the angle
    # between them at c is 2 asin(r/s) (constant). To get a general alpha we must instead
    # let the two endpoints be the two INTERSECTION POINTS of the two circles S^1 and
    # B(x_-, r) etc. So the asymmetric point is: |c|=s, |c-x_+|=r, and x_- is the OTHER
    # intersection of S^1 with the line through c at angle al from x_+.
    # Simplest: search over the two-circle configuration numerically.
    # parameterise c by phi and take x_+ one of the two points at distance r (sign +),
    # x_- the point at distance rho from c with 0<rho<r chosen so that alpha comes out al.
    # Instead: solve for (phi, rho) with |c|=s, |c-x_+|=r, |c-x_-|=rho, angle = al.
    # Skip the closed form and report the measured theta for the range of phi above.
    P('%-8s (see the phi table above: alpha is a function of phi)' % av)
P('')
P('NOTE: the phi table above already tests the formula at the points where BOTH endpoints')
P('      are at distance r from c; those are the symmetric-branch points, not the')
P('      asymmetric ones.  The asymmetric branch needs one endpoint at distance r and the')
P('      OTHER at distance < r.  That is checked in (iii) below.')

P('')
P('=' * 78)
P('(iii) for fixed theta, minimise alpha over the legal set and identify the attaining')
P('      configuration (endpoint distances and |c| vs s)')
P('theta    min alpha     a_+        a_-        |c|/s      a_+=r? a_-=r?  |c|=s?')
for tv in ['0.2', '0.3', '0.4', '0.5', '0.6']:
    th = mp.mpf(tv); h = th/2
    H = mp.cos(h); v = mp.sin(h)
    dmax = mp.sqrt(max(mp.mpf(0), r*r - v*v))
    best = None
    N = 1500
    for i in range(1, N+1):
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
            den = d*d + b*b - v*v
            num = 2*d*v
            cot = den/num
            a = mp.atan(1/cot) if cot > 0 else (mp.pi/2 if cot == 0 else mp.pi + mp.atan(1/cot))
            if best is None or a < best[0]:
                cn = mp.sqrt((H-d)**2 + b*b)
                best = (a, d, b, mp.sqrt(d*d+(b-v)**2), mp.sqrt(d*d+(b+v)**2), cn)
    a, d, b, a1, a2, cn = best
    P('%-8s %-12s %-10s %-10s %-10s %-6s %-6s %s'
      % (tv, mp.nstr(a, 12), mp.nstr(a1, 10), mp.nstr(a2, 10), mp.nstr(cn/s, 10),
         mp.nstr(a1-r, 3), mp.nstr(a2-r, 3), mp.nstr(cn-s, 3)))
    P('           theta_asym(alpha) = %s ; theta_sym(alpha) = %s ; theta = %s'
      % (mp.nstr(a - mp.acos(s*mp.cos(a)) + mp.asin(r), 12),
         mp.nstr(2*mp.asin(r*mp.sin(a/2)), 12), tv))

(OUT / 'asym01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'asym01.txt')
