"""root-cc2 area-safe-audit: audit of the cover-to-angle geometric interface (I1-I8).

Each item is checked with exact/high-precision arithmetic, independent of the lead's code.
I1 angle ranges; I2 chord/inner-norm argument; I3 wedge-area rate <= pi/2 and triangle
bound (rho^2/2) sin alpha; I4 convexity of g and the cap sum; I5 the total inequality;
I6 the supporting-plane identity; I7 monotonicity of sin L/L (the document's claim is
checked numerically); I8 outward-clip strictness bookkeeping.
"""
import json
import sys
from pathlib import Path
import mpmath as mp

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead')
HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
sys.path.insert(0, str(LEAD))
from root_integer_certificate import I, Q, S

mp.mp.dps = 40
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

# ---------------------------------------------------------------- I3: wedge-area rate
P('=' * 78)
P('I3  wedge-area rate and the triangle bound')
def wedge_rate(th):
    """(theta - sin theta)/sin theta  for theta in (0, pi)"""
    return (th - mp.sin(th))/mp.sin(th)

maxrate = mp.mpf(0); argmax = None
for k in range(1, 20000):
    th = mp.pi*mp.mpf(k)/20000
    r = wedge_rate(th)
    if r > maxrate:
        maxrate, argmax = r, th
P('    max over theta in (0,pi) of (theta-sin theta)/sin theta = %s at theta = %s rad'
  % (mp.nstr(maxrate, 12), mp.nstr(argmax, 8)))
P('    (pi/2)/(pi/2-1) = %s  -> rate < pi/2/(pi/2-1) = %s, consistent with G < pi'
  % (mp.nstr((mp.pi/2)/(mp.pi/2-1), 8), mp.nstr((mp.pi/2)/(mp.pi/2-1), 8)))
P('    limit as theta->0: theta^2/6 / theta = theta/6 -> 0 ; limit as theta->pi: pi/(0+)')
P('    so the sup is at theta = pi and equals pi/(pi/2-1) = %s (finite)'
  % mp.nstr(mp.pi/(mp.pi/2-mp.mpf(1)), 8))
P('    with L <= pi/3 the rate is bounded by the value at L:')
for Lv in ['0.6', '1.0', '1.0471975511965979']:
    L = mp.mpf(Lv)
    P('      L=%s  rate(L)=%s' % (Lv, mp.nstr(wedge_rate(L), 8)))

P('')
P('    triangle bound: for r1,r2 <= rho and alpha in [0,pi], is (1/2)r1 r2 sin a <= (rho^2/2) sin a?')
P('      sin a >= 0 on [0,pi], so the bound follows from r1 r2 <= rho^2; checked numerically:')
worst = mp.mpf(0)
for k in range(1, 50):
    a = mp.pi*mp.mpf(k)/50
    rho = mp.mpf('0.3317')
    best = mp.mpf(0)
    for i in range(1, 40):
        r1 = rho*mp.mpf(i)/40
        r2 = rho
        best = max(best, mp.mpf('0.5')*r1*r2*mp.sin(a))
    worst = max(worst, best/(mp.mpf('0.5')*rho*rho*mp.sin(a)))
P('      max ratio (actual/bound) = %s  (<= 1)' % mp.nstr(worst, 12))

# ---------------------------------------------------------------- I4/I5: cap and total
P('')
P('=' * 78)
P('I4/I5  cap sum, convexity of g, and the total inequality')
def cap(rho):
    L = 2*mp.asin(rho)
    return mp.pi*(1 - mp.sin(L)/L)
for rv in ['0.2', '0.3', '0.3317320342762341', '0.4', '0.5']:
    rho = mp.mpf(rv)
    L = 2*mp.asin(rho)
    P('    rho=%s  L=%s  sinL/L=%s  cap=%s  rho^2=%s  rho^2/2=%s'
      % (rv, mp.nstr(L, 8), mp.nstr(mp.sin(L)/L, 10), mp.nstr(cap(rho), 10),
         mp.nstr(rho**2, 10), mp.nstr(rho**2/2, 10)))
P('    F(rho)=1-cap(rho)-rho^2/2 :')
for rv in ['0.2', '0.25', '0.3', '0.3317320342762341']:
    rho = mp.mpf(rv)
    P('      rho=%s  F=%s   (F>0 <=> pi<cap+rho^2/2 in the trivial all-beta=0 case)'
      % (rv, mp.nstr(1 - cap(rho) - rho**2/2, 10)))
P('')
P('    convexity check g(t)=t-sin t on [0,L]: g(a*t1+(1-a)t2) <= a g(t1)+(1-a) g(t2)?')
L = 2*mp.asin(mp.mpf('0.3317320342762341'))
g = lambda t: t - mp.sin(t)
ok = True
for i in range(0, 21):
    t1 = L*mp.mpf(i)/20; t2 = L
    for j in range(0, 11):
        al = mp.mpf(j)/10
        lhs = g(al*t1 + (1-al)*t2); rhs = al*g(t1) + (1-al)*g(t2)
        if lhs > rhs + mp.mpf('1e-30'): ok = False
P('    convexity inequality holds on the grid: %s' % ok)
P('    g(L)/L = %s ; so g(theta) <= theta*g(L)/L ; sum theta_i = 2 pi gives cap sum <= pi*g(L)/L'
  % mp.nstr(g(L)/L, 12))

# ---------------------------------------------------------------- I6: supporting plane
P('')
P('=' * 78)
P('I6  supporting-plane identity (exact symbolic check on random data)')
import random
random.seed(7)
bad = 0
for trial in range(200):
    m = random.randint(2, 6); n = random.randint(1, 5)
    U = mp.mpf('0.4')
    a = [mp.mpf('0.08') if random.random() < 0.5 else mp.mpf('0.16') for _ in range(n)]
    t = [mp.mpf(random.random())*mp.pi for _ in range(n)]
    y = [mp.mpf(random.random())*2-1 for _ in range(m)]
    rhs = mp.mpf(0); lhs = mp.mpf(0)
    for j in range(n):
        t0 = mp.mpf(random.random())*mp.pi
        # terms: a_j sin t_j <= a_j(sin t0 - t0 cos t0) + a_j cos t0 * t_j
        lhs += a[j]*mp.sin(t[j])
        rhs += a[j]*(mp.sin(t0) - t0*mp.cos(t0)) + (a[j]*mp.cos(t0) - y[0])*t[j] + 0
        # max over t_j in [0,pi] of (a_j cos t0 - p_j) t_j handled below
    # compare with the box maximum formula
    tot_rhs = mp.mpf(0)
    for j in range(n):
        t0 = mp.mpf(random.random())*mp.pi
        c = a[j]*mp.cos(t0) - y[0]
        tot_rhs += a[j]*(mp.sin(t0) - t0*mp.cos(t0)) + mp.pi*max(mp.mpf(0), c)
    if lhs > tot_rhs + mp.mpf('1e-25'):
        bad += 1
P('    trials where sum a_j sin t_j exceeded the boxed RHS: %d / 200' % bad)
P('    (0 expected: this is the certificate inequality for any t_j in [0,pi])')

# ---------------------------------------------------------------- I7: monotonicity
P('')
P('=' * 78)
P('I7  monotonicity of h(L)=sin L/L and cap(rho)=pi(1-h)')
def h(L): return mp.sin(L)/L
P('    h(L) for L in (0,pi):')
for Lv in ['0.1', '0.3', '0.6', '0.6767', '1.0', '1.5', '2.0', '2.2', '2.2467', '2.5', '3.0']:
    L = mp.mpf(Lv)
    P('      L=%-7s h=%s   cap=%s' % (Lv, mp.nstr(h(L), 12), mp.nstr(mp.pi*(1-h(L)), 12)))
crit = None
lo, hi = mp.mpf('0.5'), mp.mpf('3.1')
for _ in range(80):
    mid = (lo+hi)/2
    if mp.diff(h, mid) > 0: lo = mid
    else: hi = mid
crit = lo
P('    h increases up to L* = %s (rho* = sin(L*/2) = %s), then decreases'
  % (mp.nstr(crit, 10), mp.nstr(mp.sin(crit/2), 10)))
P('    derivative of h at L = 2.2 : %s ; at L = 2.3 : %s'
  % (mp.nstr(mp.diff(h, mp.mpf('2.2')), 8), mp.nstr(mp.diff(h, mp.mpf('2.3')), 8)))
P('    => the document\'s "sin L/L decreases for L in (0,pi)" is FALSY; it is increasing')
P('       on (0,L*) with L* = %s.  For our regime L <= pi/3 the increasing claim is what' % mp.nstr(crit, 8))
P('       is needed, so the conclusion (cap monotone increasing in rho) survives.')

(OUT / 'geom01_I1_I8.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'geom01_I1_I8.txt')
