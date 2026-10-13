"""root-cc2 innernorm-envelope: the exact envelope and its structure.

Two branch bounds (verified numerically below):
  L1(alpha) = alpha - arccos(s cos alpha) + asin r      (inner-norm branch, one endpoint tight)
  L2(alpha) = 2 asin(r sin(alpha/2))                    (equal-endpoint-radii branch)
and the true envelope is the MINIMUM:  theta <= min(L1(alpha), L2(alpha))  (both bounds
hold simultaneously at the configuration's own alpha).
L2 has the closed form pi - alpha on [alpha*, pi] where alpha* solves L1 = L2.
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
L1 = lambda a: a - mp.acos(s*mp.cos(a)) + mp.asin(r)
L2 = lambda a: 2*mp.asin(r*mp.sin(a/2))
L1p = lambda a: 1 + s*mp.sin(a)/mp.sqrt(1 - s*s*mp.cos(a)**2)
L2p = lambda a: r*mp.cos(a/2)/mp.sqrt(1 - r*r*mp.sin(a/2)**2)

P('=' * 78)
P('r = %s ; s = %s' % (mp.nstr(r, 12), mp.nstr(s, 12)))
a1 = mp.findroot(lambda a: L1p(a) - 1, mp.mpf('0.8'), solver='anderson')
P('critical point of L1 (L1\' = 1):  alpha_1 = %s ; L1 = %s ; L1\' = %s'
  % (mp.nstr(a1, 12), mp.nstr(L1(a1), 12), mp.nstr(L1p(a1), 12)))
astar = mp.findroot(lambda a: L1(a) - L2(a), mp.mpf('1.3'), solver='anderson')
P('switch point (L1 = L2):  alpha* = %s' % mp.nstr(astar, 12))
P('  L1(alpha*) = %s ; L2(alpha*) = %s ; pi - alpha* = %s'
  % (mp.nstr(L1(astar), 12), mp.nstr(L2(astar), 12), mp.nstr(mp.pi - astar, 12)))
P('  check L2(alpha) = pi - alpha near alpha*: L2 = %s, pi-alpha = %s'
  % (mp.nstr(L2(astar + mp.mpf('0.01')), 12), mp.nstr(mp.pi - astar - mp.mpf('0.01'), 12)))

P('')
P('=' * 78)
P('(1) which branch is the envelope min, and its concavity')
P('alpha    L1          L2          min        L1<=L2?')
prev = None
for av in ['0.05', '0.15', '0.3', '0.5', '0.7', '0.9', '1.1', '1.3', '1.5', '1.9', '2.4', '2.9', '3.14']:
    a = mp.mpf(av)
    P('%-8s %-11s %-11s %-10s %s' % (av, mp.nstr(L1(a), 10), mp.nstr(L2(a), 10),
                                     mp.nstr(min(L1(a), L2(a)), 10), L1(a) <= L2(a)))

P('')
P('(2) concavity of the envelope E(alpha) = min(L1, L2)')
P('    on [0, alpha*]: E = L1, E\'\' = ? ; on [alpha*, pi]: E = L2, E\'\' = ?')
def L1pp(a):
    # d/da [1 + s sin a / sqrt(1 - s^2 cos^2 a)]
    f = s*mp.sin(a); g = mp.sqrt(1 - s*s*mp.cos(a)**2)
    return mp.diff(lambda x: L1p(x), a)
def L2pp(a):
    return mp.diff(lambda x: L2p(x), a)
P('    alpha    L1\'\'        L2\'\'        E\'\' (min branch)')
for av in ['0.05', '0.2', '0.4', '0.6', '0.7', '0.9', '1.2', '1.6', '2.2', '2.8']:
    a = mp.mpf(av)
    e2 = L1pp(a) if a < astar else L2pp(a)
    P('    %-8s %-11s %-11s %s' % (av, mp.nstr(L1pp(a), 10), mp.nstr(L2pp(a), 10), mp.nstr(e2, 10)))
P('')
P('    L1 is convex up to alpha_1 = %s then concave; L2 is concave on [0,pi].' % mp.nstr(a1, 8))
P('    => E = min(L1,L2) is concave on [0,alpha*] only while L1 is concave there, i.e.')
P('       provided alpha_1 <= alpha*: %s (alpha_1 = %s, alpha* = %s)'
  % (a1 <= astar, mp.nstr(a1, 8), mp.nstr(astar, 8)))

P('')
P('=' * 78)
P('(3) verification: for a fine grid of alpha, construct the point with')
P('    |c| = s, |c - x_+| = r and angle alpha, measure theta, compare with L1(alpha)')
P('    (This rebuilds the asymmetric configuration explicitly.)')
P('alpha    theta_measured   L1(alpha)      diff')
for av in ['0.1', '0.3', '0.5', '0.7', '0.9', '1.1']:
    al = mp.mpf(av)
    # c on circle of radius s; the two unit points at distance r from c are at angles
    # phi +- asin(r/s).  We need angle at c between (x_+ - c) and (x_- - c) = al where
    # x_- is an arbitrary unit point.  Parameterise instead:  choose x_+ unit, then c is
    # on the circle of radius r about x_+ AND on |c| = s: two choices.  Then x_- is the
    # unit point making angle al at c; solve for it.
    # We instead scan x_- over the unit circle and record (alpha, theta) pairs for which
    # both |c-x_+| = r and |c| = s hold.
    best = None
    N = 4000
    for i in range(1, N):
        psi = mp.pi*mp.mpf(i)/N           # x_+ at angle psi
        xp = (mp.cos(psi), mp.sin(psi))
        # c: intersection of B(0,s) and B(xp,r)
        k = (1 + s*s - r*r)/2
        # x.c = k  -> c = k*xp +- sqrt(s^2-k^2) * perp(xp)
        hh = mp.sqrt(max(mp.mpf(0), s*s - k*k))
        for sgn in (1, -1):
            perp = (-xp[1], xp[0])
            c = (k*xp[0] + sgn*hh*perp[0], k*xp[1] + sgn*hh*perp[1])
            # x_- on the unit circle with angle al at c from (xp - c)
            u = (xp[0]-c[0], xp[1]-c[1]); nu = mp.sqrt(u[0]**2+u[1]**2)
            n0 = mp.pi/2 - al if False else None
            # direction of w = rotate u by +-al
            for sg in (1, -1):
                ca = mp.cos(sg*al); sa = mp.sin(sg*al)
                w = (u[0]*ca - u[1]*sa, u[0]*sa + u[1]*ca)
                # x_- = c + t*w, |x_-| = 1
                A = w[0]**2 + w[1]**2
                B = 2*(c[0]*w[0] + c[1]*w[1])
                C = c[0]**2 + c[1]**2 - 1
                disc = B*B - 4*A*C
                if disc < 0: continue
                for t in ((-B + mp.sqrt(disc))/(2*A), (-B - mp.sqrt(disc))/(2*A)):
                    if t <= 0: continue
                    xm = (c[0] + t*w[0], c[1] + t*w[1])
                    d = mp.acos(max(mp.mpf(-1), min(mp.mpf(1), xp[0]*xm[0] + xp[1]*xm[1])))
                    if abs(d - al) < mp.mpf('1e-12'):
                        if best is None or abs(c[0]) + abs(c[1]) < best[0]:
                            best = (abs(c[0]) + abs(c[1]), d)
    if best is None:
        P('%-8s (no configuration found)' % av)
    else:
        P('%-8s %-16s %-14s %s' % (av, mp.nstr(best[1], 12), mp.nstr(L1(al), 12),
                                   mp.nstr(best[1]-L1(al), 6)))

(OUT / 'asym02.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'asym02.txt')
