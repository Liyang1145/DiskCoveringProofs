"""root-cc2 innernorm-envelope: exact envelope structure (bisection-based, no findroot).

Branches:
  L1(alpha) = alpha - arccos(s cos alpha) + asin r        (inner-norm branch)
  L2(alpha) = 2 asin(r sin(alpha/2))                      (equal-radius branch)
Envelope: theta <= min(L1, L2).  L1' = 1 + s sin a / sqrt(1 - s^2 cos^2 a) = 1 at a = pi/2.
L1'' at pi/2 = -s sqrt(1-s^2) ... (computed below); L2'' <= 0.
"""
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)
mp.mp.dps = 50
log = []
def P(*a):
    s2 = ' '.join(str(x) for x in a); print(s2); log.append(s2)

def bisect(f, lo, hi, n=200):
    flo = f(lo)
    for _ in range(n):
        mid = (lo+hi)/2
        fm = f(mid)
        if flo*fm <= 0: hi = mid
        else: lo = mid; flo = fm
    return (lo+hi)/2

r = mp.mpf('0.33173203427623414'); s = mp.sqrt(1-r*r)
L1 = lambda a: a - mp.acos(s*mp.cos(a)) + mp.asin(r)
L2 = lambda a: 2*mp.asin(r*mp.sin(a/2))
L1p = lambda a: 1 + s*mp.sin(a)/mp.sqrt(1 - s*s*mp.cos(a)**2)
L2p = lambda a: r*mp.cos(a/2)/mp.sqrt(1 - r*r*mp.sin(a/2)**2)

P('=' * 78)
P('r = %s ; s = %s' % (mp.nstr(r, 12), mp.nstr(s, 12)))
P('')
P('(1) branch data')
P('    alpha    L1           L1\'          L2           L2\'          min branch')
for av in ['0.05', '0.2', '0.4', '0.6', '0.8', '1.0', '1.2', '1.5', '2.0', '2.5', '3.0', '3.14']:
    a = mp.mpf(av)
    P('    %-8s %-12s %-12s %-12s %-12s %s'
      % (av, mp.nstr(L1(a), 10), mp.nstr(L1p(a), 10), mp.nstr(L2(a), 10), mp.nstr(L2p(a), 10),
         'L1' if L1(a) <= L2(a) else 'L2'))
a1 = mp.pi/2
P('')
P('    L1\'(pi/2) = %s  (so the critical point of L1 is exactly pi/2)' % mp.nstr(L1p(a1), 20))
P('    L1(pi/2) = %s' % mp.nstr(L1(a1), 12))
P('    L2(pi/2) = %s' % mp.nstr(L2(a1), 12))
P('    so on [0,pi/2] L1 <= L2 and on [pi/2,pi] L2 <= L1:  switch at alpha* = pi/2')
P('    check: L1(0)=%s L2(0)=%s ; L1(pi)=%s L2(pi)=%s'
  % (mp.nstr(L1(mp.mpf(0)), 10), mp.nstr(L2(mp.mpf(0)), 10),
     mp.nstr(L1(mp.pi), 10), mp.nstr(L2(mp.pi), 10)))
astar = bisect(lambda a: L1(a) - L2(a), mp.mpf('0.1'), mp.mpf('2.9'))
P('    numerical switch point: %s' % mp.nstr(astar, 12))

P('')
P('(2) envelope E = min(L1, L2) and its second derivative')
P('    alpha    E            E\'\'')
for av in ['0.05', '0.2', '0.4', '0.6', '0.8', '1.0', '1.2', '1.6', '2.2', '2.8']:
    a = mp.mpf(av)
    E = lambda x: min(L1(x), L2(x))
    e2 = mp.diff(E, a, 2)
    P('    %-8s %-12s %s' % (av, mp.nstr(E(a), 10), mp.nstr(e2, 10)))
P('')
P('    E is concave on [0,pi]: E = L1 on [0,pi/2] (L1 concave from pi/2 onwards?) and')
P('    L2 on [pi/2,pi] (L2 concave everywhere).  L1\'\' at pi/2: %s'
  % mp.nstr(mp.diff(L1, mp.pi/2, 2), 12))
P('    L1\'\' is negative for alpha < pi/2 too?  values: %s'
  % [mp.nstr(mp.diff(L1, mp.mpf(x), 2), 8) for x in ['0.05', '0.2', '0.4', '0.6']])

P('')
P('(3) monotone inversion: theta -> alpha_min')
P('    theta   alpha_min (solve E(alpha)=theta on the correct branch)')
for tv in ['0.05', '0.1', '0.2', '0.2969', '0.4', '0.6', '0.9', '1.2']:
    th = mp.mpf(tv)
    if th <= L2(mp.pi/2):
        a = bisect(lambda x: L1(x) - th, mp.mpf('1e-9'), mp.pi/2)
    else:
        a = bisect(lambda x: L2(x) - th, mp.pi/2, mp.pi)
    P('    %-8s %s' % (tv, mp.nstr(a, 12)))

P('')
P('(4) verification against direct minimisation over the legal region')
P('    theta    alpha_min(formula)   alpha_min(grid)   diff')
def amin_grid(th, N=1200, M=300):
    h = th/2; H = mp.cos(h); v = mp.sin(h)
    dmax = mp.sqrt(max(mp.mpf(0), r*r - v*v))
    best = None
    for i in range(1, N+1):
        d = dmax*mp.mpf(i)/N
        w = mp.sqrt(max(mp.mpf(0), r*r - d*d))
        blo = max(mp.mpf(0), v - w); bhi = w - v
        if bhi < blo: continue
        Q = 2*H*d + v*v - r*r
        bN = mp.sqrt(Q - d*d) if Q - d*d > 0 else mp.mpf(0)
        bm = min(bhi, bN)
        if bm < blo: continue
        for j in range(0, M+1):
            b = blo + (bm - blo)*mp.mpf(j)/M
            cot = (d*d + b*b - v*v)/(2*d*v)
            a = mp.atan(1/cot) if cot > 0 else (mp.pi/2 if cot == 0 else mp.pi + mp.atan(1/cot))
            if best is None or a < best[0]: best = (a, d, b)
    return best[0]
for tv in ['0.2', '0.3', '0.5', '0.9', '1.2']:
    th = mp.mpf(tv)
    if th <= L2(mp.pi/2):
        af = bisect(lambda x: L1(x) - th, mp.mpf('1e-9'), mp.pi/2)
    else:
        af = bisect(lambda x: L2(x) - th, mp.pi/2, mp.pi)
    ag = amin_grid(th)
    P('    %-8s %-20s %-18s %s' % (tv, mp.nstr(af, 12), mp.nstr(ag, 12), mp.nstr(af-ag, 6)))

(OUT / 'env_final.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'env_final.txt')
