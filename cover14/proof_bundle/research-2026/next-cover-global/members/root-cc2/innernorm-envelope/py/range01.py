"""root-cc2 innernorm-envelope: small, exact-ish settlement of the branch relation.

Q: for a fixed viewing angle alpha, is THETA_MAX(alpha) = max(A,B) or min(A,B)?
Method (no global scan): for each h on a grid, compute the legal (d,b) set and the range
of alpha attained; for a target alpha, the configuration exists at that h iff alpha lies
in the attained range. Report theta_max(alpha) = max 2h over h whose alpha-range contains
alpha, using an efficient per-h computation.
"""
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)
mp.mp.dps = 30
log = []
def P(*a):
    x = ' '.join(str(z) for z in a); print(x); log.append(x)

r = mp.mpf('0.33173203427623414'); s = mp.sqrt(1-r*r); u = mp.asin(r)
A = lambda x: x - mp.acos(s*mp.cos(x)) + u
B = lambda x: 2*mp.asin(r*mp.sin(x/2))
def alpha_of(d, b, H, v):
    dot = d*d + b*b - v*v; cr = 2*d*v
    if dot > 0: return mp.atan(cr/dot)
    return mp.pi + mp.atan(cr/dot) if dot < 0 else mp.pi/2

# For each h, alpha ranges over [alpha_min(h), alpha_max(h)] as (d,b) varies in the legal
# region (cot is continuous).  alpha is decreasing in cot, so alpha_min corresponds to
# max cot and vice versa.
P('=' * 78)
P('per-h alpha range and the corresponding theta')
P('h        theta      alpha_min     alpha_max    A(alpha_min) B(alpha_min)  A(alpha_max) B(alpha_max)')
rows = []
NH = 160
for i in range(1, NH+1):
    h = u*mp.mpf(i)/NH
    v = mp.sin(h); H = mp.cos(h)
    D = mp.sqrt(max(mp.mpf(0), r*r - v*v)); lo = max(mp.mpf(0), H - s)
    if D <= lo: continue
    amins = []; amaxs = []
    for k in range(0, 81):
        d = lo + (D-lo)*mp.mpf(k)/80
        if d <= 0: continue
        w = mp.sqrt(max(mp.mpf(0), r*r - d*d)); bhi = w - v
        if bhi < 0: continue
        Q = 2*H*d + v*v - r*r
        bN = mp.sqrt(Q-d*d) if Q-d*d > 0 else mp.mpf(0)
        bm = min(bhi, bN)
        if bm < 0: continue
        for j in range(0, 21):
            b = bm*mp.mpf(j)/20
            amins.append(alpha_of(d, b, H, v))
    if not amins: continue
    amin = min(amins); amax = max(amins)
    rows.append((h, amin, amax))
for (h, amin, amax) in rows[::8]:
    P('%-8s %-10s %-13s %-13s %-13s %-13s %-13s %s'
      % (mp.nstr(h, 6), mp.nstr(2*h, 8), mp.nstr(amin, 10), mp.nstr(amax, 10),
         mp.nstr(A(amin), 8), mp.nstr(B(amin), 8), mp.nstr(A(amax), 8), mp.nstr(B(amax), 8)))

P('')
P('For a target alpha, theta_max(alpha) = max{2h : alpha in [amin(h), amax(h)]}')
P('The monotone shape of the range tells us which branch attains it.')
P('alpha    theta_max      A(alpha)     B(alpha)     branch')
for t in ['0.1', '0.2', '0.3', '0.5', '0.8', '1.0', '1.3', '1.7']:
    al = mp.mpf(t); best = None
    for (h, amin, amax) in rows:
        if amin <= al <= amax:
            if best is None or h > best: best = h
    if best is None:
        P('%-8s none' % t); continue
    th = 2*best
    P('%-8s %-14s %-12s %-12s %s' % (t, mp.nstr(th, 10), mp.nstr(A(al), 10), mp.nstr(B(al), 10),
       'A' if abs(th-A(al)) < abs(th-B(al)) else 'B'))

(OUT / 'range01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'range01.txt')
