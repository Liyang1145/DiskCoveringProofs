"""root-cc2 innernorm-envelope: authoritative THETA_MAX(alpha) scan (correct alpha).

alpha = atan2(|u x w|, u.w) with u = x_+ - c, w = x_- - c.  For each alpha-bin we record
the largest theta = 2h over all legal (h,d,b).  Compared against A(alpha), B(alpha).
"""
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)
mp.mp.dps = 25
log = []
def P(*a):
    x = ' '.join(str(z) for z in a); print(x); log.append(x)

r = mp.mpf('0.33173203427623414'); s = mp.sqrt(1-r*r); u = mp.asin(r)
A = lambda x: x - mp.acos(s*mp.cos(x)) + u
B = lambda x: 2*mp.asin(r*mp.sin(x/2))
def alpha_of(d, b, H, v):
    uu = (d, v-b); ww = (d, -v-b)
    cr = abs(uu[0]*ww[1] - uu[1]*ww[0]); dot = uu[0]*ww[0] + uu[1]*ww[1]
    return mp.atan2(cr, dot)

P('=' * 78)
P('THETA_MAX(alpha): fine scan (correct alpha), compared to A and B')
Nbin = 24
bins = {}
NH = 400
for i in range(1, NH+1):
    h = u*mp.mpf(i)/NH
    v = mp.sin(h); H = mp.cos(h); th = 2*h
    D = mp.sqrt(max(mp.mpf(0), r*r - v*v)); lo = max(mp.mpf(0), H - s)
    if D <= lo: continue
    for k in range(0, 121):
        d = lo + (D-lo)*mp.mpf(k)/120
        if d <= 0: continue
        w = mp.sqrt(max(mp.mpf(0), r*r - d*d)); bhi = w - v
        if bhi < 0: continue
        Q = 2*H*d + v*v - r*r
        bN = mp.sqrt(Q-d*d) if Q-d*d > 0 else mp.mpf(0)
        bm = min(bhi, bN)
        if bm < 0: continue
        for j in range(0, 21):
            b = bm*mp.mpf(j)/20
            al = alpha_of(d, b, H, v)
            ib = int(float(al)*Nbin/mp.pi)
            if ib >= Nbin: ib = Nbin - 1
            if ib not in bins or th > bins[ib]:
                bins[ib] = th
P('alpha          theta_max    A(alpha)   B(alpha)   max(A,B)   min(A,B)   |th-A|   |th-B|')
for ib in range(Nbin):
    al = mp.pi*(mp.mpf(ib)+mp.mpf('0.5'))/Nbin
    if ib not in bins: continue
    th = bins[ib]
    P('%-14s %-12s %-10s %-10s %-10s %-10s %-8s %s'
      % (mp.nstr(al, 6), mp.nstr(th, 8), mp.nstr(A(al), 8), mp.nstr(B(al), 8),
         mp.nstr(max(A(al), B(al)), 8), mp.nstr(min(A(al), B(al)), 8),
         mp.nstr(abs(th-A(al)), 4), mp.nstr(abs(th-B(al)), 4)))

(OUT / 'authoritative_scan.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'authoritative_scan.txt')
