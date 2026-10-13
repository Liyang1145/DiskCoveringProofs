"""root-cc2 innernorm-envelope: independent verification of the exact affine majorant.

Line to certify:  theta <= A + k alpha,  A = 135/1000, k = 218/1000.
Conditions needed (for max(a,b) <= A + k alpha on [0,pi]):
  C1  A + k a0 >= tangent_a(a0)  for the a-tangent at a0 = 0.458   (a concave on [0,pi/2])
  C2  tangent_a(a0) >= a(pi)                                        (a convex on [pi/2,pi]:
                                                                     the max there is at an
                                                                     endpoint, so checking
                                                                     a(pi) and a(pi/2) suffices)
  C3  tangent_a(a0) >= a(pi/2)
  C4  A + k b0 >= tangent_b(b0)  for the b-tangent at b0 = 1.77     (b concave on [0,pi])
All verified here with mpmath at 60 digits, and the final line checked directly on [0,pi].
"""
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)
mp.mp.dps = 60
log = []
def P(*a):
    x = ' '.join(str(z) for z in a); print(x); log.append(x)

r = mp.mpf('0.33173203427623414'); s = mp.sqrt(1-r*r); u = mp.asin(r)
a = lambda x: x - mp.acos(s*mp.cos(x)) + u
b = lambda x: 2*mp.asin(r*mp.sin(x/2))
ap = lambda x: 1 - s*mp.sin(x)/mp.sqrt(1 - s*s*mp.cos(x)**2)
bp = lambda x: r*mp.cos(x/2)/mp.sqrt(1 - r*r*mp.sin(x/2)**2)
A = mp.mpf('0.135'); k = mp.mpf('0.218')

P('=' * 78)
P('r = %s ; s = %s ; u = %s' % (mp.nstr(r, 12), mp.nstr(s, 12), mp.nstr(u, 12)))
a0 = mp.mpf('0.458'); b0 = mp.mpf('1.77')
P('')
P('(1) the requested conditions')
P('    C1 A + k*a0 - a(a0)  = %s   (a-tangent at %s lies below the line)'
  % (mp.nstr(A + k*a0 - a(a0), 12), mp.nstr(a0, 6)))
P('    C2 a-tangent(a0) - a(pi) = %s' % mp.nstr((a(a0) + ap(a0)*(mp.pi-a0)) - a(mp.pi), 12))
P('    C3 a-tangent(a0) - a(pi/2) = %s' % mp.nstr((a(a0) + ap(a0)*(mp.pi/2-a0)) - a(mp.pi/2), 12))
P('    C4 A + k*b0 - b(b0)  = %s' % mp.nstr(A + k*b0 - b(b0), 12))
P('    also A - a(0) = %s (a(0)=0) ; A - b(0) = %s' % (mp.nstr(A - a(0), 10), mp.nstr(A - b(0), 10)))
P('')
P('(2) direct check of max(a,b) <= A + k alpha on [0,pi]')
worst = None
N = 400000
for i in range(N+1):
    x = mp.pi*mp.mpf(i)/N
    lhs = max(a(x), b(x)); rhs = A + k*x
    if worst is None or lhs - rhs > worst[0]:
        worst = (lhs-rhs, x, lhs, rhs)
P('    max excess (max(a,b) - line) = %s at alpha = %s' % (mp.nstr(worst[0], 10), mp.nstr(worst[1], 10)))
P('    line = %s ; value = %s ; margin = %s' % (mp.nstr(worst[3], 10), mp.nstr(worst[2], 10), mp.nstr(worst[3]-worst[2], 10)))
P('    LINE VALID on the grid: %s' % (worst[0] <= 0))
P('')
P('(3) the two curvature facts')
P('    a\'\'(alpha) = -s r^2 cos(alpha)/[1-s^2 cos^2 alpha]^{3/2} < 0 on [0,pi/2], > 0 on [pi/2,pi]')
P('      a\'\'(0.3) = %s ; a\'\'(1.6) = %s ; a\'\'(pi/2) = %s'
  % (mp.nstr(mp.diff(a, mp.mpf('0.3'), 2), 10), mp.nstr(mp.diff(a, mp.mpf('1.6'), 2), 10),
     mp.nstr(mp.diff(a, mp.pi/2, 2), 10)))
P('    b\'\'(alpha) = %s at alpha=1 ; max on grid (should be <=0): %s'
  % (mp.nstr(mp.diff(b, mp.mpf(1), 2), 10),
     mp.nstr(max(mp.diff(b, mp.pi*mp.mpf(i)/2000, 2) for i in range(2001)), 10)))
P('')
P('(4) which branch is tight: switch point of a and b')
lo, hi = mp.mpf('0.5'), mp.mpf('1.5')
for _ in range(300):
    m = (lo+hi)/2
    if (a(lo)-b(lo))*(a(m)-b(m)) <= 0: hi = m
    else: lo = m
astar = (lo+hi)/2
P('    a = b at alpha* = %s ; theta* = %s' % (mp.nstr(astar, 12), mp.nstr(a(astar), 12)))
P('    a < b for alpha < alpha* (a binds) ; b < a for alpha > alpha* (b binds)')
P('    => min(alpha_a(theta), alpha_b(theta)) and theta <= max(a,b) are equivalent.')

(OUT / 'line01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'line01.txt')
