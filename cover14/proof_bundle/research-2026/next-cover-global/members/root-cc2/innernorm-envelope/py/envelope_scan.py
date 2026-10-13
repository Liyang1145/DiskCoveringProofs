"""root-cc2 innernorm-envelope: compute THETA_MAX(alpha) directly from feasibility.

For a configuration c=(H-d,b), the three conditions are
   (i)  d^2 + (b-v)^2 <= r^2
   (ii) d^2 + (b+v)^2 <= r^2
   (iii)d^2 + b^2     <= 2Hd + v^2 - r^2
with H = cos h, v = sin h, theta = 2h.

For fixed d (in [H-s, D] with D = sqrt(r^2-v^2)) the v-interval is obtained from:
   (ii) v <= sqrt(r^2-d^2) - b     [b >= 0]
   (iii) v^2 - 2Hd v + (d^2+b^2+r^2-2Hd) <= 0  -> v <= Hd + sqrt((Hd)^2 - (d^2+b^2)+r^2-2Hd)
Here we simply scan (h, d, b) on a fine grid and record, for each bin of alpha, the
largest theta.  This directly measures the envelope without assuming either branch.
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
    dot = d*d + b*b - v*v
    cr = 2*d*v
    if dot > 0: return mp.atan(cr/dot)
    return mp.pi + mp.atan(cr/dot) if dot < 0 else mp.pi/2

P('=' * 78)
P('THETA_MAX(alpha): scan h on a fine grid; for each h scan the legal (d,b) box')
Nbin = 32
bins = {}
NH = 700
for i in range(1, NH+1):
    h = u*mp.mpf(i)/NH
    v = mp.sin(h); H = mp.cos(h)
    D = mp.sqrt(max(mp.mpf(0), r*r - v*v))
    lo = max(mp.mpf(0), H - s)
    if D <= lo: continue
    for k in range(0, 141):
        d = lo + (D-lo)*mp.mpf(k)/140
        if d <= 0: continue
        w = mp.sqrt(max(mp.mpf(0), r*r - d*d))
        bhi = w - v
        if bhi < 0: continue
        Q = 2*H*d + v*v - r*r
        bN = mp.sqrt(Q-d*d) if Q-d*d > 0 else mp.mpf(0)
        bm = min(bhi, bN)
        if bm < 0: continue
        for j in range(0, 21):
            b = bm*mp.mpf(j)/20
            al = alpha_of(d, b, H, v)
            ib = int(float(al)*Nbin/mp.pi)
            if ib >= Nbin: ib = Nbin-1
            if ib not in bins or 2*h > bins[ib]:
                bins[ib] = 2*h

P('alpha(bin centre)   theta_max(scan)   A(alpha)     B(alpha)    theta-A     theta-B')
for ib in range(Nbin):
    al = mp.pi*(mp.mpf(ib)+mp.mpf('0.5'))/Nbin
    if ib not in bins: continue
    th = bins[ib]
    P('%-18s %-17s %-12s %-12s %-11s %s'
      % (mp.nstr(al, 6), mp.nstr(th, 8), mp.nstr(A(al), 8), mp.nstr(B(al), 8),
         mp.nstr(th-A(al), 5), mp.nstr(th-B(al), 5)))

P('')
P('Interpretation: theta_max(alpha) should equal max(A,B) if both branches are attainable')
P('at that alpha, and min(A,B) if only the smaller is attainable.')

(OUT / 'envelope_scan.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'envelope_scan.txt')
