"""root-cc2 innernorm-envelope: the decisive computation.

For a fine grid of alpha, find THETA_MAX(alpha) = the largest theta over legal
configurations with viewing angle alpha, and compare with A(alpha), B(alpha).
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

P('=' * 78)
P('THETA_MAX(alpha) on a fine alpha grid, from a fine (h,d,b) scan')
targets = ['0.05', '0.1', '0.2', '0.3', '0.5', '0.7', '0.9', '1.0', '1.2', '1.5', '1.9', '2.4', '2.9']
best = {t: None for t in targets}
NH = 900
for i in range(1, NH+1):
    h = u*mp.mpf(i)/NH
    v = mp.sin(h); H = mp.cos(h); th = 2*h
    D = mp.sqrt(max(mp.mpf(0), r*r - v*v)); lo = max(mp.mpf(0), H - s)
    if D <= lo: continue
    for k in range(0, 201):
        d = lo + (D-lo)*mp.mpf(k)/200
        if d <= 0: continue
        w = mp.sqrt(max(mp.mpf(0), r*r - d*d)); bhi = w - v
        if bhi < 0: continue
        Q = 2*H*d + v*v - r*r
        bN = mp.sqrt(Q-d*d) if Q-d*d > 0 else mp.mpf(0)
        bm = min(bhi, bN)
        if bm < 0: continue
        for j in range(0, 31):
            b = bm*mp.mpf(j)/30
            al = alpha_of(d, b, H, v)
            for t in targets:
                tv = mp.mpf(t)
                if abs(al-tv) < mp.mpf('5e-3'):
                    if best[t] is None or th > best[t][0]:
                        best[t] = (th, d, b, h)
P('alpha    theta_max(scan)   A(alpha)     B(alpha)    max(A,B)   theta-max(A,B)')
for t in targets:
    if best[t] is None:
        P('%-8s none' % t); continue
    th = best[t][0]; al = mp.mpf(t)
    P('%-8s %-17s %-12s %-12s %-11s %s'
      % (t, mp.nstr(th, 10), mp.nstr(A(al), 10), mp.nstr(B(al), 10),
         mp.nstr(max(A(al), B(al)), 10), mp.nstr(th-max(A(al), B(al)), 6)))
P('')
P('Finer confirmation near alpha = 0.2 and 0.5 with a tighter tolerance:')
for t in ['0.2', '0.5']:
    tv = mp.mpf(t); bb = None
    for i in range(1, 3000):
        h = u*mp.mpf(i)/3000
        v = mp.sin(h); H = mp.cos(h); th = 2*h
        D = mp.sqrt(max(mp.mpf(0), r*r - v*v)); lo = max(mp.mpf(0), H - s)
        if D <= lo: continue
        for k in range(0, 301):
            d = lo + (D-lo)*mp.mpf(k)/300
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
                if abs(al-tv) < mp.mpf('2e-3'):
                    if bb is None or th > bb[0]: bb = (th, d, b)
    if bb:
        P('  alpha=%s theta_max=%s  max(A,B)=%s  diff=%s'
          % (t, mp.nstr(bb[0], 10), mp.nstr(max(A(tv), B(tv)), 10),
             mp.nstr(bb[0]-max(A(tv), B(tv)), 6)))

(OUT / 'theta_max.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'theta_max.txt')
