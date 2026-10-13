"""root-cc2 innernorm-envelope: correct objective.

The viewing angle alpha in cot form: for x_pm = (H, +-v) and c = (H-d, b), d>0, b>=0,

    cot alpha = (d^2 + b^2 - v^2) / (2 d v).

We MINIMISE cot alpha (equivalently maximise alpha in [0,pi]) over the legal region:
    (D) d^2 + (b -+ v)^2 <= r^2  (covers both endpoints)
    (N) d^2 + b^2 <= 2 H d + v^2 - r^2  (inner norm |c| <= s, H^2+v^2=1, s^2=1-r^2)
    d > 0, b >= 0.

Numerically we locate the minimiser and compare with the four candidate branches:
  equal endpoint radii (d^2+(b+v)^2 = d^2+(b-v)^2 = r^2, i.e. b=0, d^2=r^2-v^2)
  one endpoint tight + inner norm
  inner norm alone
  domain endpoint
"""
import sys
from pathlib import Path
import mpmath as mp

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
mp.mp.dps = 40
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

U = mp.mpf('0.33173203427623414'); r = U
S = mp.sqrt(1 - r*r)
HMAX = mp.asin(r)
P('=' * 78)
P('r = %s ; s = %s ; h_max = asin(r) = %s (= theta_max/2)' % (mp.nstr(r, 12), mp.nstr(S, 12), mp.nstr(HMAX, 12)))
P('cot alpha = (d^2+b^2-v^2)/(2 d v)  ;  minimise over the legal region')
P('')
P('(1) grid minimisation of cot alpha')
P('    h      theta     min cot      argmin (d,b)          |c|      a         b_       |c|=s?')
for hv in ['0.05', '0.10', '0.166', '0.20', '0.25', '0.30', '0.338']:
    h = mp.mpf(hv)
    if h > HMAX: P('    %s beyond h_max' % hv); continue
    H = mp.cos(h); v = mp.sin(h)
    best = None
    dmax = mp.sqrt(r*r - v*v)
    N = 500
    for i in range(1, N+1):
        d = dmax*mp.mpf(i)/N
        if d <= 0: continue
        # admissible b: (D) |b - v| <= sqrt(r^2-d^2) and b <= v + sqrt(...)
        sw = mp.sqrt(max(mp.mpf(0), r*r - d*d))
        blo = max(mp.mpf(0), v - sw)
        bhi = v + sw
        # (N): d^2 + b^2 <= 2Hd + v^2 - r^2 =: Q  -> b <= sqrt(max(0,Q-d^2))
        Q = 2*H*d + v*v - r*r
        bN = mp.sqrt(max(mp.mpf(0), Q - d*d)) if Q - d*d > 0 else mp.mpf(0)
        bmax = min(bhi, bN)
        if bmax < blo:
            continue
        for j in range(0, 201):
            b = blo + (bmax - blo)*mp.mpf(j)/200
            cot = (d*d + b*b - v*v)/(2*d*v)
            if best is None or cot < best[0]:
                a1 = mp.sqrt(d*d + (b+v)**2); a2 = mp.sqrt(d*d + (b-v)**2)
                best = (cot, d, b, a1, a2)
    if best is None:
        P('    %-6s no legal point' % hv); continue
    cot, d, b, a1, a2 = best
    cnorm = mp.sqrt((H-d)**2 + b*b)
    P('    %-6s %-7s %-12s (%.6f, %.6f)  %-8s %-9s %-9s %s'
      % (hv, mp.nstr(2*h, 6), mp.nstr(cot, 10), float(d), float(b), mp.nstr(cnorm, 8),
         mp.nstr(a1, 8), mp.nstr(a2, 8), mp.nstr(cnorm - S, 4)))
    P('           alpha = acot = %s  (theta = %s ; theta-alpha = %s)'
      % (mp.nstr(mp.acot(cot), 10), mp.nstr(2*h, 8), mp.nstr(2*h - mp.acot(cot), 8)))

P('')
P('=' * 78)
P('(2) the candidate branches at the same h values')
for hv in ['0.05', '0.10', '0.166', '0.20', '0.25', '0.30', '0.338']:
    h = mp.mpf(hv)
    if h > HMAX: continue
    H = mp.cos(h); v = mp.sin(h)
    P('    h = %-7s v = %-10s' % (hv, mp.nstr(v, 8)))
    # E1: both endpoints tight: b = 0, d = sqrt(r^2 - v^2)
    d1 = mp.sqrt(r*r - v*v)
    c1 = (H-d1, mp.mpf(0))
    cot1 = (d1*d1 - v*v)/(2*d1*v) if d1 > 0 else mp.inf
    P('       E1 both-tight (b=0,d=sqrt(r^2-v^2)=%s): cot = %s  alpha = %s  |c|=%s (<=s: %s)'
      % (mp.nstr(d1, 8), mp.nstr(cot1, 10), mp.nstr(mp.acot(cot1), 10),
         mp.nstr(abs(H-d1), 8), abs(H-d1) <= S))
    # E2: inner norm alone (b=0, |c|=s): (H-d)^2 = s^2
    d2 = H - S
    if d2 > 0:
        cot2 = (d2*d2 - v*v)/(2*d2*v)
        a1 = mp.sqrt(d2*d2 + v*v)
        P('       E2 inner-norm (b=0,|c|=s,d=H-s=%s): cot = %s  alpha = %s  endpoint dist = %s (<=r: %s)'
          % (mp.nstr(d2, 8), mp.nstr(cot2, 10), mp.nstr(mp.acot(cot2), 10),
             mp.nstr(a1, 8), a1 <= r))
    else:
        P('       E2 inner-norm: d = H-s = %s <= 0, infeasible' % mp.nstr(d2, 8))
    # E3: one endpoint tight + inner norm (solve d^2+(b+v)^2=r^2 with d^2+b^2=2Hd+v^2-r^2)
    # subtract: 2bv = 2Hd - 2r^2 + 2v^2  -> b = (Hd - r^2 + v^2)/v ; substitute in (D)
    # solve numerically
    def eq(d):
        # from d^2+(b+v)^2 = r^2 with b = (H d - r^2 + v^2)/v
        bb = (H*d - r*r + v*v)/v
        return d*d + (bb+v)**2 - r*r
    # bracket
    lo, hi = mp.mpf('1e-8'), d1
    f_lo, f_hi = eq(lo), eq(hi)
    if f_lo*f_hi < 0:
        for _ in range(300):
            mid = (lo+hi)/2
            if eq(lo)*eq(mid) <= 0: hi = mid
            else: lo = mid
        d3 = (lo+hi)/2
        b3 = (H*d3 - r*r + v*v)/v
        if b3 >= 0:
            cot3 = (d3*d3 + b3*b3 - v*v)/(2*d3*v)
            a1 = mp.sqrt(d3*d3 + (b3+v)**2); a2 = mp.sqrt(d3*d3 + (b3-v)**2)
            cnorm = mp.sqrt((H-d3)**2 + b3*b3)
            P('       E3 one-tight+norm (d=%s,b=%s): cot = %s alpha = %s  |c|=%s  a1=%s a2=%s'
              % (mp.nstr(d3, 8), mp.nstr(b3, 8), mp.nstr(cot3, 10), mp.nstr(mp.acot(cot3), 10),
                 mp.nstr(cnorm, 8), mp.nstr(a1, 8), mp.nstr(a2, 8)))
        else:
            P('       E3: b<0, not in the domain')
    else:
        P('       E3: no sign change on (0, d1)')

(OUT / 'explore03.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'explore03.txt')
