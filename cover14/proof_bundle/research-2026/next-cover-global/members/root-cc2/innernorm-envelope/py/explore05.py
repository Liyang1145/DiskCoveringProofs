"""root-cc2 innernorm-envelope: CORRECTED admissible b range.

Coordinates: x_pm = (H, +-v), H = cos h, v = sin h; c = (H-d, b), d > 0, b >= 0.
    cot alpha = (d^2 + b^2 - v^2)/(2 d v)
Legal region:
    |c - x_+|^2 = d^2 + (b - v)^2 <= r^2      ->  b in [v - w, v + w]
    |c - x_-|^2 = d^2 + (b + v)^2 <= r^2      ->  b in [-v - w, w - v]
    (w = sqrt(r^2 - d^2))
  => b in [max(0, v - w), w - v]  and this is nonempty iff w >= v.
    |c|^2 = (H-d)^2 + b^2 <= s^2 = 1 - r^2  ->  d^2 + b^2 <= 2 H d + v^2 - r^2.
(The earlier run used the wrong upper limit v + w; that is the bug this fixes.)
Objective: minimise alpha in [0,pi].
"""
import sys
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)
mp.mp.dps = 40
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

U = mp.mpf('0.33173203427623414'); r = U
S = mp.sqrt(1 - r*r); HMAX = mp.asin(r)

def alpha_of(d, b, v):
    u = (d, v - b); w = (d, -v - b)
    nu = mp.sqrt(u[0]**2 + u[1]**2); nw = mp.sqrt(w[0]**2 + w[1]**2)
    cs = (u[0]*w[0] + u[1]*w[1])/(nu*nw)
    return mp.acos(max(mp.mpf(-1), min(mp.mpf(1), cs)))

P('=' * 78)
P('r = %s ; s = %s ; h_max = asin r = %s (= half the cap L)' % (mp.nstr(r, 12), mp.nstr(S, 12), mp.nstr(HMAX, 12)))
P('')
P('(1) min alpha over the legal set (grid) and the candidate points')
P('    h      theta   min_alpha(grid)  argmin (d,b)         |c|       a_+       a_-     E1: pi/2-h   E2(norm)')
for hv in ['0.05', '0.10', '0.166', '0.20', '0.25', '0.30', '0.338']:
    h = mp.mpf(hv)
    if h > HMAX: P('    %s beyond h_max' % hv); continue
    H = mp.cos(h); v = mp.sin(h)
    dmax = mp.sqrt(max(mp.mpf(0), r*r - v*v))
    best = None
    N = 800
    for i in range(0, N+1):
        d = dmax*mp.mpf(i)/N
        w = mp.sqrt(max(mp.mpf(0), r*r - d*d))
        blo = max(mp.mpf(0), v - w)
        bhi = w - v
        if bhi < blo: continue
        Q = 2*H*d + v*v - r*r
        bN = mp.sqrt(Q - d*d) if Q - d*d > 0 else mp.mpf(0)
        bm = min(bhi, bN)
        if bm < blo: continue
        for j in range(0, 201):
            b = blo + (bm - blo)*mp.mpf(j)/200
            a = alpha_of(d, b, v)
            if best is None or a < best[0]:
                nu = mp.sqrt(d*d + (b-v)**2); nw = mp.sqrt(d*d + (b+v)**2)
                cn = mp.sqrt((H-d)**2 + b*b)
                best = (a, d, b, cn, nu, nw)
    a, d, b, cn, nu, nw = best
    dE1 = dmax; aE1 = alpha_of(dE1, mp.mpf(0), v)
    dE2 = H - S
    aE2 = alpha_of(dE2, mp.mpf(0), v) if dE2 > 0 else None
    P('    %-6s %-7s %-16s (%.6f,%.6f) %-9s %-9s %-9s %-12s %s'
      % (hv, mp.nstr(2*h, 6), mp.nstr(a, 10), float(d), float(b), mp.nstr(cn, 8),
         mp.nstr(nu, 8), mp.nstr(nw, 8), mp.nstr(mp.pi/2 - h, 10),
         mp.nstr(aE2, 8) if aE2 is not None else 'n/a'))
    P('           E1 (b=0,d=sqrt(r^2-v^2)) alpha = %s ; is the grid argmin E1? d:%s b:%s'
      % (mp.nstr(aE1, 10), mp.nstr(abs(d-dE1), 4), mp.nstr(b, 4)))
    P('           norm active at argmin? |c|=%s vs s=%s ; b vs b_N: %s'
      % (mp.nstr(cn, 8), mp.nstr(S, 8), mp.nstr(b - mp.sqrt(max(mp.mpf(0), 2*H*d + v*v - r*r - d*d)), 4)))

P('')
P('=' * 78)
P('(2) checks of the branch formulas')
h = mp.mpf('0.05'); H = mp.cos(h); v = mp.sin(h)
P('    h=0.05 both-tight cot = (r^2-2v^2)/(2 v sqrt(r^2-v^2)) = %s ; alpha = %s'
  % (mp.nstr((r*r-2*v*v)/(2*v*mp.sqrt(r*r-v*v)), 10), mp.nstr(mp.pi/2 - h, 10)))
P('    alpha = pi/2 - h requires pi/2-h <= pi (true) and the inscribed-angle geometry;')
P('    the numeric column above tests it.')
P('')
P('    inner-norm branch cot = H/v - r^2/(2 d v) (if |c| = s is imposed);')
h = mp.mpf('0.10'); H = mp.cos(h); v = mp.sin(h)
d = H - S
P('    h=0.10, d=H-s=%s: cot = %s ; the disk-branch formula instead gives' % (mp.nstr(d, 8), mp.nstr(H/v - r*r/(2*d*v), 10)))
P('      [r^2-2v sqrt(r^2-d^2)]/(2 v d) = %s'
  % mp.nstr((r*r-2*v*mp.sqrt(r*r-d*d))/(2*v*d), 10))

(OUT / 'explore05.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'explore05.txt')
