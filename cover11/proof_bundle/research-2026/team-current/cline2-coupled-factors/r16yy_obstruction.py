"""cline2-coupled-factors R16yy: pin the k-interval obstruction and test local validity.

r16xx shows no single k works on the whole legal set.  This script:
  1. verifies the two obstructing witnesses (are they legal? what is their status?);
  2. reports the exact maximal k-interval per face from the sample;
  3. tests the criterion in the NEIGHBOURHOOD of the stationary points (where the
     integrating-factor argument is actually needed), with a bounded local k.
"""
import math, json, sys
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
sys.path.insert(0, str(P))
from r16xx_kcriterion import V_derivs, legal, k_interval

OUT = P / 'out'

print('=== 1. the two obstructing witnesses ===')
wits = [(1, mp.mpf('0.37916666666666665'), mp.mpf('1.0'), mp.mpf('1.0'), mp.mpf('-0.25')),
        (2, mp.mpf('0.375'), mp.mpf('1.0'), mp.mpf('1.0'), mp.mpf('0.25')),
        (1, mp.mpf('0.37833333333333335'), mp.mpf('1.02285'), mp.mpf('1.0'),
         mp.mpf('-0.34257')),
        (2, mp.mpf('0.38'), mp.mpf('1.02263'), mp.mpf('1.0'), mp.mpf('0.41584'))]
for (face, rv, b1v, b2v, dv) in wits:
    ok = legal(rv, b1v, b2v, dv, face)
    res = V_derivs(rv, b1v, b2v, dv, face)
    G, Gp, Gpp = res
    print(f'  face {face} r={float(rv):.6f} b1={float(b1v):.5f} b2={float(b2v):.5f} '
          f'd={float(dv):+.5f}: legal={ok}')
    print(f'      G={mp.nstr(G,12)}  G\'={mp.nstr(Gp,12)}  G\'\'={mp.nstr(Gpp,12)}  '
          f'-G\'\'/G\'={mp.nstr(-Gpp/Gp,10)}')
    # exact admissibility residuals
    A = b1v-dv; B = b2v+dv
    H = 2*rv*mp.sin(2*b1v-dv) if face == 1 else 2*rv*mp.sin(2*b2v+dv)
    s = mp.sqrt(1-rv*rv)
    R1 = 2*rv*mp.sin(2*b1v-dv)-H
    R2 = 2*rv*mp.sin(2*b2v+dv)-H
    N = 2*s*mp.cos(dv)*H-H*H-2*rv*(1-rv)
    print(f'      residuals: R1={mp.nstr(R1,8)} R2={mp.nstr(R2,8)} N={mp.nstr(N,8)}')
    # is delta = 0 in the legal range?  is this point near a zero of G'?
    print(f'      G\' sign: {"positive" if Gp > 0 else "negative"}; '
          f'|G\'|={mp.nstr(abs(Gp),8)}')

print()
print('=== 2. maximal k-interval per face (from the same 200-point samples) ===')
sys.argv = ['x']
import random
random.seed(2024)
for face in (1, 2):
    cand = []
    for i in range(7):
        rv = mp.mpf(str(0.375+(0.38-0.375)*i/6))
        bhi = float(mp.acos(rv))
        for a in range(9):
            b1v = mp.mpf(str(1.0+(bhi-1.0)*a/8))
            for c in range(9):
                b2v = mp.mpf(str(1.0+(bhi-1.0)*c/8))
                for m in range(41):
                    dv = mp.mpf(str(-b2v+(b1v+b2v)*m/40))
                    cand.append((rv, b1v, b2v, dv))
    random.shuffle(cand)
    sign = 1 if face == 1 else -1
    pts = []
    for (rv, b1v, b2v, dv) in cand:
        if len(pts) >= 200:
            break
        if not legal(rv, b1v, b2v, dv, face):
            continue
        res = V_derivs(rv, b1v, b2v, dv, face)
        if res is None:
            continue
        pts.append((rv, b1v, b2v, dv, res[1]*sign, res[2]))
    need_above = max((-g2/g1) for (_, _, _, _, g1, g2) in pts if g1 > 0)
    need_below = min((-g2/g1) for (_, _, _, _, g1, g2) in pts if g1 < 0)
    npos = sum(1 for (_, _, _, _, g1, g2) in pts if g1 > 0)
    nneg = len(pts)-npos
    print(f'  face {face}: {len(pts)} legal pts ({npos} with G\'>0, {nneg} with G\'<0)')
    print(f'     k must EXCEED   {mp.nstr(need_above,10)}   (from the G\'>0 points)')
    print(f'     k must be BELOW {mp.nstr(need_below,10)}   (from the G\'<0 points)')
    print(f'     -> nonempty: {need_above < need_below}')

print()
print('=== 3. is the criterion valid in the NEIGHBOURHOOD of the stationary points? ===')
print('   (the integrating-factor argument is only needed where G\' changes sign)')
for face in (1, 2):
    sign = 1 if face == 1 else -1
    print(f'  face {face}:')
    for (rv, b1v, b2v) in [(mp.mpf('0.379'), mp.mpf('1.0'), mp.mpf('1.0')),
                           (mp.mpf('0.375'), mp.mpf('1.0'), mp.mpf('1.0')),
                           (mp.mpf('0.377'), mp.mpf('1.02285'), mp.mpf('1.0'))]:
        # locate the zero of G' in delta by bisection on the legal range
        lo, hi = -b2v, mp.mpf(0)
        def Gp_of(d):
            res = V_derivs(rv, b1v, b2v, d, face)
            return None if res is None else res[1]*sign
        a, b = lo, hi
        fa, fb = Gp_of(a), Gp_of(b)
        if fa is None or fb is None or fa*fb > 0:
            print(f'     r={float(rv)} b1={float(b1v)} b2={float(b2v)}: '
                  f'no sign change of G on [{float(lo)},{float(hi)}] '
                  f'(G(lo)={None if fa is None else float(fa):.4f}, '
                  f'G(hi)={None if fb is None else float(fb):.4f})')
            continue
        for _ in range(80):
            m = (a+b)/2
            fm = Gp_of(m)
            if fm is None:
                break
            if fa*fm <= 0:
                b = m; fb = fm
            else:
                a = m; fa = fm
        d0 = (a+b)/2
        res = V_derivs(rv, b1v, b2v, d0, face)
        ratio = -res[2]*sign/(res[1]*sign) if res[1] != 0 else None
        print(f'     r={float(rv)} b1={float(b1v):.5f} b2={float(b2v):.5f}: '
              f'G\' zero at d={float(d0):+.6f}  G\'\'={mp.nstr(res[2],10)}  '
              f'legal={legal(rv, b1v, b2v, d0, face)}')
        # the ratio along a window around d0
        worst = 0
        wpt = None
        for k in range(-20, 21):
            dk = d0+mp.mpf(k)*mp.mpf('0.002')
            rr = V_derivs(rv, b1v, b2v, dk, face)
            if rr is None:
                continue
            g1 = rr[1]*sign; g2 = rr[2]
            if g1 != 0:
                val = -g2/g1
                if g1 > 0 and val > worst:
                    worst = val; wpt = (float(dk), float(g1), float(g2))
        print(f'        max (-G\'\'/G\') over a +-0.04 window about the zero: '
              f'{worst:.6f} at {wpt}')
