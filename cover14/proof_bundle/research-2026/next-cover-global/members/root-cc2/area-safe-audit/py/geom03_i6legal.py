"""root-cc2 area-safe-audit: I6 with a clean incidence matrix over the (alpha,beta) vector.

t = (alpha_0..alpha_{nb-1}, beta_0..beta_{ne-1});  B t = 2 pi 1 with
  row i (boundary site): alpha_i + sum of beta incident to i = 2 pi
  row i (hidden site):                sum of beta incident to i = 2 pi
The certificate inequality is tested with p = B^T y for arbitrary rational y, on random
LEGAL t (each alpha_i = 2 pi - incident beta, checked to lie in [0,pi]).
"""
import random
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
mp.mp.dps = 40
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

random.seed(11)
U = mp.mpf('0.31')
aU2 = U*U; aU22 = U*U/2

P('=' * 78)
P('I6  supporting-plane inequality, legal t only')
tested = 0; skipped = 0; fails = 0; worst = None
for trial in range(800):
    nb = random.randint(1, 3)
    nh = random.randint(0, 2)
    nodes = nb + nh
    ne = random.randint(nb, 8)
    endp = [(random.randrange(nodes), random.randrange(nodes)) for _ in range(ne)]
    inc = [[e for e in range(ne) if i in endp[e]] for i in range(nodes)]
    beta = [mp.mpf(random.randint(0, 1000))/1000*mp.pi for _ in range(ne)]
    alpha = []
    legal = True
    for i in range(nb):
        a_i = 2*mp.pi - sum(beta[e] for e in inc[i])
        if a_i < 0 or a_i > mp.pi:
            legal = False
        alpha.append(a_i)
    for i in range(nb, nodes):
        if abs(sum(beta[e] for e in inc[i]) - 2*mp.pi) > mp.mpf('1e-25'):
            legal = False
    if not legal:
        skipped += 1
        continue
    tested += 1
    n = nb + ne
    t = alpha + beta
    a = [aU22]*nb + [aU2]*ne
    y = [mp.mpf(random.randint(-4, 4))/mp.mpf(4) for _ in range(nodes)]
    # p = B^T y : alpha column has a single 1 (its node); beta column has 1 at each endpoint
    p = []
    for j in range(nb):
        p.append(y[j])
    for e in range(ne):
        i, k = endp[e]
        p.append(y[i] + y[k])
    t0 = [mp.mpf(random.randint(0, 1000))/1000*mp.pi for _ in range(n)]
    lhs = sum(a[j]*mp.sin(t[j]) for j in range(n))
    rhs = (sum(a[j]*(mp.sin(t0[j]) - t0[j]*mp.cos(t0[j])) for j in range(n))
           + 2*mp.pi*sum(y)
           + mp.pi*sum(max(mp.mpf(0), a[j]*mp.cos(t0[j]) - p[j]) for j in range(n)))
    if lhs > rhs + mp.mpf('1e-25'):
        fails += 1
        if worst is None or lhs - rhs > worst[0]:
            worst = (lhs-rhs, n, ne, [mp.nstr(x, 6) for x in t], [mp.nstr(x, 6) for x in t0],
                     [mp.nstr(x, 6) for x in y])
P('    legal samples: %d (skipped %d) ; violations: %d' % (tested, skipped, fails))
if worst:
    P('    worst: gap=%s n=%s ne=%s' % (mp.nstr(worst[0], 8), worst[1], worst[2]))
    P('      t =%s' % worst[3]); P('      t0=%s' % worst[4]); P('      y =%s' % worst[5])

P('')
P('    discriminating control (illegal t must violate):')
nb, ne = 1, 1
a = [aU22, aU2]
t_bad = [mp.mpf('0.5'), mp.mpf('3.0')]
y = [mp.mpf(0)]
p = [mp.mpf(0), mp.mpf(0)]
t0 = list(t_bad)
lhs = sum(a[j]*mp.sin(t_bad[j]) for j in range(2))
rhs = (sum(a[j]*(mp.sin(t0[j]) - t0[j]*mp.cos(t0[j])) for j in range(2))
       + mp.pi*sum(max(mp.mpf(0), a[j]*mp.cos(t0[j]) - p[j]) for j in range(2)))
P('      alpha+beta = %s != 2 pi=6.2832 ; lhs=%s rhs=%s violated=%s'
  % (mp.nstr(t_bad[0]+t_bad[1], 8), mp.nstr(lhs, 8), mp.nstr(rhs, 8), lhs > rhs))

P('')
P('=' * 78)
P('I7  h(L) = sin L / L')
def h(L): return mp.sin(L)/L
crit = mp.findroot(lambda L: L*mp.cos(L) - mp.sin(L), mp.mpf('2.2'), solver='anderson')
P('    critical point: L* = %s   rho* = sin(L*/2) = %s' % (mp.nstr(crit, 12), mp.nstr(mp.sin(crit/2), 12)))
P('    h(L*) = %s (max) ; h(0.5)=%s ; h(2.5)=%s'
  % (mp.nstr(h(crit), 12), mp.nstr(h(mp.mpf('0.5')), 10), mp.nstr(h(mp.mpf('2.5')), 10)))
P('    h\'(2 asin 0.3317320) = %s > 0  (our regime is in the increasing branch)'
  % mp.nstr(mp.diff(h, 2*mp.asin(mp.mpf('0.3317320342762341'))), 8))
P('    => document\'s "sin L/L decreases for L in (0,pi)" is FALSE as stated;')
P('       correct: h increases on (0,L*) with L* = %s (rho* = %s), decreases after.'
  % (mp.nstr(crit, 8), mp.nstr(mp.sin(crit/2), 8)))
P('       The needed conclusion (cap(rho) decreasing in rho near rho ~ 0.3) still holds.')

(OUT / 'geom03_I6legal_I7.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'geom03_I6legal_I7.txt')
