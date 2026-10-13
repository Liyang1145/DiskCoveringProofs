"""root-cc2 innernorm-envelope: settle the envelope direction (min vs max) by brute force.

For a fixed alpha, compute THETA_MAX(alpha) = max over legal c of the angle central
subtended-- i.e. the largest covered arc with viewing angle alpha.  Then compare with
a_r(alpha) and b_r(alpha) declared in the note.  Also test the two-point inversion
variants against the grid minimum.
"""
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)
mp.mp.dps = 40
log = []
def P(*a):
    x = ' '.join(str(z) for z in a); print(x); log.append(x)

r = mp.mpf('0.33173203427623414'); s = mp.sqrt(1-r*r); u = mp.asin(r)
def afun(x): return x - mp.acos(s*mp.cos(x)) + u
def bfun(x): return 2*mp.asin(r*mp.sin(x/2))

def alpha_direct(d, b, h):
    H = mp.cos(h); v = mp.sin(h)
    uu = (d, v-b); ww = (d, -v-b)
    nu = mp.sqrt(uu[0]**2+uu[1]**2); nw = mp.sqrt(ww[0]**2+ww[1]**2)
    cs = (uu[0]*ww[0]+uu[1]*ww[1])/(nu*nw)
    return mp.acos(max(mp.mpf(-1), min(mp.mpf(1), cs)))

def theta_for(d, b, h):
    e1 = d*d + (b-mp.sin(h))**2
    e2 = d*d + (b+mp.sin(h))**2
    cn = mp.sqrt((mp.cos(h)-d)**2 + b*b)
    ok = e1 <= r*r + mp.mpf('1e-28') and e2 <= r*r + mp.mpf('1e-28') and cn <= s + mp.mpf('1e-28')
    return ok

# theta_max(alpha): scan h and (d,b) and record the largest h for which a legal point
# has viewing angle exactly alpha
P('=' * 78)
P('THETA_MAX(alpha) by brute force, versus a_r(alpha) and b_r(alpha)')
P('alpha    theta_max     a_r          b_r        theta_max-a  theta_max-b')
for av in ['0.1', '0.2', '0.3296', '0.5', '0.7', '0.92034', '0.9346', '1.0', '1.3', '1.68']:
    al = mp.mpf(av)
    best = None
    NH = 900
    for i in range(1, NH+1):
        h = u*mp.mpf(i)/NH          # theta = 2h ranges over (0, 2u)
        v = mp.sin(h); H = mp.cos(h)
        dmax = mp.sqrt(max(mp.mpf(0), r*r - v*v))
        if dmax <= 0: continue
        for k in range(1, 300):
            d = dmax*mp.mpf(k)/300
            w = mp.sqrt(max(mp.mpf(0), r*r - d*d))
            blo = max(mp.mpf(0), v-w); bhi = w-v
            if bhi < blo: continue
            Q = 2*H*d + v*v - r*r
            bN = mp.sqrt(Q-d*d) if Q-d*d > 0 else mp.mpf(0)
            bm = min(bhi, bN)
            if bm < blo: continue
            for j in range(0, 60):
                b = blo + (bm-blo)*mp.mpf(j)/60
                al2 = alpha_direct(d, b, h)
                if abs(al2-al) < mp.mpf('2e-3'):
                    if best is None or h > best[0]:
                        best = (h, d, b)
    if best is None:
        P('%-8s (none found)' % av); continue
    h = best[0]
    P('%-8s %-13s %-12s %-12s %-12s %s'
      % (av, mp.nstr(2*h, 10), mp.nstr(afun(al), 10), mp.nstr(bfun(al), 10),
         mp.nstr(2*h-afun(al), 6), mp.nstr(2*h-bfun(al), 6)))

P('')
P('=' * 78)
P('grid minimum inversion check: alpha_min(theta) vs the two candidate formulas')
def amin_grid(th, N=1500, M=500):
    h = th/2; H = mp.cos(h); v = mp.sin(h)
    dmax = mp.sqrt(r*r-v*v); best = None
    for i in range(1, N+1):
        d = dmax*mp.mpf(i)/N
        w = mp.sqrt(max(mp.mpf(0), r*r-d*d))
        blo = max(mp.mpf(0), v-w); bhi = w-v
        if bhi < blo: continue
        Q = 2*H*d+v*v-r*r
        bN = mp.sqrt(Q-d*d) if Q-d*d > 0 else mp.mpf(0)
        bm = min(bhi, bN)
        if bm < blo: continue
        for j in range(0, M+1):
            b = blo + (bm-blo)*mp.mpf(j)/M
            al = alpha_direct(d, b, h)
            if best is None or al < best[0]: best = (al, d, b)
    return best
def inv(f, th):
    # find alpha with f(alpha) = th
    lo, hi = mp.mpf('1e-12'), mp.pi
    for _ in range(300):
        m = (lo+hi)/2
        if f(m) < th: lo = m
        else: hi = m
    return (lo+hi)/2
P('theta    alpha_min(grid)  inv_a        inv_b       min(inv)     max(inv)')
for tv in ['0.1', '0.2', '0.25', '0.2969', '0.32', '0.4', '0.5']:
    th = mp.mpf(tv)
    best = amin_grid(th)
    if best is None:
        P('%-8s (grid failed)' % tv); continue
    ia = inv(afun, th); ib = inv(bfun, th)
    P('%-8s %-16s %-12s %-12s %-12s %s'
      % (tv, mp.nstr(best[0], 12), mp.nstr(ia, 10), mp.nstr(ib, 10),
         mp.nstr(min(ia, ib), 10), mp.nstr(max(ia, ib), 10)))

(OUT / 'direction01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'direction01.txt')
