"""root-cc2 chord-envelope-audit: independent verification of the envelope constants and
the geometric lemmas, in mpmath (not the lead's I type), no sampling premises.

L1/L2 convexity of (a,b) -> a^2+b^2-2ab cos(alpha) on [0,r]^2, corner maximum
L3    chord/arc transfer on the unit circle
L4    concavity of f(alpha) = 2 asin(U sin(alpha/2))
L5    exact constants A < 167/500, 0 < f'(alpha0) < 31/250, f(a0)-a0 f'(a0) < 167/500
L6    the affine envelope max(A, f(alpha)) <= 167/500 + (31/250) alpha on [0,pi]
"""
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
mp.mp.dps = 60
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

U = mp.mpf('0.33173203427623414')
r = mp.mpf('0.33173203427623414')
P('=' * 78)
P('L1/L2  convexity of g(a,b)=a^2+b^2-2ab cos(alpha) on [0,r]^2')
P('       Hessian eigenvalues 2(1-cos alpha), 2(1+cos alpha), both >= 0 for alpha in [0,pi]')
for a in ['0', '0.5', '1.5707963267948966', '3.141592653589793']:
    an = mp.mpf(a)
    e1 = 2*(1-mp.cos(an)); e2 = 2*(1+mp.cos(an))
    P('       alpha=%-20s eigenvalues %-14s %-14s PSD=%s'
      % (a, mp.nstr(e1, 8), mp.nstr(e2, 8), e1 >= -mp.mpf('1e-30') and e2 >= -mp.mpf('1e-30')))
P('       corner values and grid max (grid is support only):')
for a in ['0', '0.6', '1.2', '2.42', '3.141592653589793']:
    an = mp.mpf(a)
    g = lambda x, y: x*x + y*y - 2*x*y*mp.cos(an)
    corners = [g(0, 0), g(r, 0), g(0, r), g(r, r)]
    gm = mp.mpf(0); N = 60
    for i in range(N+1):
        for j in range(N+1):
            gm = max(gm, g(r*mp.mpf(i)/N, r*mp.mpf(j)/N))
    P('       alpha=%-20s corner max=%-16s grid max=%-16s corner_ge_grid=%s'
      % (a, mp.nstr(max(corners), 10), mp.nstr(gm, 10), gm <= max(corners)+mp.mpf('1e-28')))
P('       corner max formula max(r^2, 4 r^2 sin^2(a/2)) at a=2.42: %s ; (r,r) value: %s'
  % (mp.nstr(max(r*r, 4*r*r*mp.sin(mp.mpf('2.42')/2)**2), 12),
     mp.nstr(r*r+r*r-2*r*r*mp.cos(mp.mpf('2.42')), 12)))

P('')
P('=' * 78)
P('L3  chord/arc transfer')
P('       unit circle: chord of minor arc theta in [0,pi] is 2 sin(theta/2); so')
P('       |x-y| <= max(r, 2r sin(a/2)) => theta <= max(2asin(r/2), 2asin(r sin(a/2)))')
for rr in ['0.1', '0.33173203427623414', '0.5', '0.9', '1.0']:
    rv = mp.mpf(rr)
    P('       r=%-22s r/2=%-12s r=%-12s argument <=1: %s'
      % (rr, mp.nstr(rv/2, 8), mp.nstr(rv, 8), rv <= 1))

P('')
P('=' * 78)
P('L4/L5/L6  envelope constants')
A = 2*mp.asin(U/2)
alpha0 = mp.mpf('2.42')
f = lambda a: 2*mp.asin(U*mp.sin(a/2))
f1 = lambda a: U*mp.cos(a/2)/mp.sqrt(1-U*U*mp.sin(a/2)**2)
f2 = lambda a: -U*(1-U*U)*mp.sin(a/2)/(2*(1-U*U*mp.sin(a/2)**2)**mp.mpf('1.5'))
P('       A = 2asin(U/2) = %s ; 167/500 = %s ; A < 167/500: %s'
  % (mp.nstr(A, 16), mp.nstr(mp.mpf(167)/500, 16), A < mp.mpf(167)/500))
P('       f1(a0) = %s ; 31/250 = %s ; 0 < f1 < 31/250: %s'
  % (mp.nstr(f1(alpha0), 16), mp.nstr(mp.mpf(31)/250, 16), 0 < f1(alpha0) < mp.mpf(31)/250))
P('       f(a0)-a0 f1(a0) = %s ; < 167/500: %s'
  % (mp.nstr(f(alpha0)-alpha0*f1(alpha0), 16), f(alpha0)-alpha0*f1(alpha0) < mp.mpf(167)/500))
P('       f2(a0) = %s <= 0: %s' % (mp.nstr(f2(alpha0), 12), f2(alpha0) <= 0))
P('       max of f2 on a fine grid: %s (<=0 => concave)'
  % mp.nstr(max(f2(mp.pi*mp.mpf(i)/2000) for i in range(2001)), 8))
P('')
P('       envelope right end: A + k pi = %s ; f(pi) = %s ; A = %s ; OK: %s'
  % (mp.nstr(A+mp.mpf(31)/250*mp.pi, 14), mp.nstr(f(mp.pi), 14), mp.nstr(A, 14),
     max(A, f(mp.pi)) <= A+mp.mpf(31)/250*mp.pi))
g0 = mp.mpf(167)/500
P('       slack at alpha=0 : 167/500 - A = %s' % mp.nstr(g0-A, 10))
P('       slack at alpha=pi: 167/500 + (31/250)pi - f(pi) = %s'
  % mp.nstr(g0+mp.mpf(31)/250*mp.pi-f(mp.pi), 10))
gfun = lambda a: g0 + mp.mpf(31)/250*a - max(A, f(a))
P('       min envelope slack over a 100001-point grid: %s'
  % mp.nstr(min(gfun(mp.pi*mp.mpf(i)/100000) for i in range(100001)), 10))
P('       slack at alpha0: %s' % mp.nstr(gfun(alpha0), 10))
P('')
P('K constants')
for q in (10, 11):
    K = (2*mp.pi - q*g0)/(mp.mpf(31)/250)
    P('       q=%d  K_q = (2pi - q*167/500)/(31/250) = %s' % (q, mp.nstr(K, 10)))

(OUT / 'env01_constants.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'env01_constants.txt')
