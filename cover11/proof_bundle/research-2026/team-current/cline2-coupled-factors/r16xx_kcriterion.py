"""cline2-coupled-factors R16xx: the integrating-factor criterion on LEGAL points.

Criterion (lead):  face1  G'' + k G' > 0 ,   face2  G'' - k G' > 0 ,  scalar k.
Rationale: writing the bracket as exp(-k delta) (G'' + k G') = (exp(-k delta) G')', a
positive bracket makes (exp(-k delta) G')' strictly positive, i.e. exp(-k delta) G' strictly
increasing.  A positive function with a strictly increasing ... argument admits at most one
zero, and each zero is crossed from - to +, so every interior stationary point is a MINIMUM
and there is at most one.  That is exactly the "stationary maximum excluded" statement.

This script, BEFORE any interval work:
  1. reproduces the lead's two Cartesian AD values at (.375,1.05,1.05,0);
  2. builds <=200 LEGAL points per face with the CORRECTED filters
     (R1 = 2r sin(2b1-dl) - H >= 0,  R2 = 2r sin(2b2+dl) - H >= 0,
      N = 2 s cos(dl) H - H^2 - 2r(1-r) >= 0) on the ACTUAL branch heights
     H = 2r sin(2b1-dl) (face 1) / 2r sin(2b2+dl) (face 2);
  3. for each legal point computes the k-interval where the criterion holds, and
     intersects them (bounded scalar interval intersection);
  4. reports the resulting k-interval -- WITHOUT assuming k = 8 works.
"""
import math, json, sys
from pathlib import Path
from mpmath import mp, iv

mp.dps = 30
iv.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
R = mp.mpf(19)/50
C0 = mp.mpf(f'{zJ[3]-zJ[1]:.9f}')
XX1 = mp.mpf(f'{zJ[1]-zJ[9]:.9f}'); XX2 = mp.mpf(f'{zJ[3]-zJ[9]:.9f}')
BE1 = mp.mpf(f'{-zJ[16]:.9f}'); GA1 = mp.mpf(f'{-zJ[78]:.9f}')
BE2 = mp.mpf(f'{zJ[20]:.9f}');  GA2 = mp.mpf(f'{zJ[82]:.9f}')
BHI = float(mp.acos(mp.mpf('0.375')))


def V_derivs(r, b1, b2, dl, face):
    """(G, G', G'') on the given arc, corrected assembly"""
    A = b1-dl; B = b2+dl
    if face == 1:
        H = 2*r*mp.sin(2*b1-dl); Hp = -2*r*mp.cos(2*b1-dl)
    else:
        H = 2*r*mp.sin(2*b2+dl); Hp = 2*r*mp.cos(2*b2+dl)
    Hpp = -H
    k = r*(mp.sin(b1)*mp.sin(A)+mp.sin(b2)*mp.sin(B))
    kp = r*(-mp.sin(b1)*mp.cos(A)+mp.sin(b2)*mp.cos(B))
    kpp = -k
    G = C0*dl+H*k
    Gp = C0+Hp*k+H*kp
    Gpp = Hpp*k+2*Hp*kp+H*kpp
    for i, (b, ang, dang, xx, bb, gg) in enumerate(
            [(b1, A, -1, XX1, BE1, GA1), (b2, B, 1, XX2, BE2, GA2)]):
        on = (face == 1 and i == 0) or (face == 2 and i == 1)
        if on:
            e = r*mp.sin(ang)/R; ep = r*mp.cos(ang)*dang/R; epp = -e
            phi = b; phip = mp.mpf(0); phipp = mp.mpf(0)
        else:
            Y = 2*r*mp.sin(b)*mp.sin(ang)
            X = H-2*r*mp.sin(b)*mp.cos(ang)
            Yp = 2*r*mp.sin(b)*mp.cos(ang)*dang
            Xp = Hp+2*r*mp.sin(b)*mp.sin(ang)*dang
            Ypp = -2*r*mp.sin(b)*mp.sin(ang)
            Xpp = Hpp+2*r*mp.sin(b)*mp.cos(ang)
            Q = X*X+Y*Y
            if Q <= 0:
                return None
            sq = mp.sqrt(Q)
            Qp = 2*(X*Xp+Y*Yp)
            Qpp = 2*(Xp*Xp+X*Xpp+Yp*Yp+Y*Ypp)
            e = sq/(2*R); ep = Qp/(4*R*sq)
            epp = Qpp/(4*R*sq)-Qp*Qp/(8*R*Q**mp.mpf('1.5'))
            num = X*Yp-Y*Xp
            nump = Xp*Yp+X*Ypp-Yp*Xp-Y*Xpp
            phi = mp.atan2(Y, X)
            phip = num/Q
            phipp = (nump*Q-num*Qp)/(Q*Q)
        G += xx*phi+bb*e*e+gg*e
        Gp += xx*phip+(2*bb*e+gg)*ep
        Gpp += xx*phipp+(2*bb*e+gg)*epp+2*bb*ep*ep
    return G, Gp, Gpp


def legal(r, b1, b2, dl, face, tol=0):
    A = b1-dl; B = b2+dl
    if A < 0 or B < 0:
        return False
    H = 2*r*mp.sin(2*b1-dl) if face == 1 else 2*r*mp.sin(2*b2+dl)
    if H <= 0 or H >= 2*r:
        return False
    s = mp.sqrt(1-r*r)
    R1 = 2*r*mp.sin(2*b1-dl)-H
    R2 = 2*r*mp.sin(2*b2+dl)-H
    N = 2*s*mp.cos(dl)*H-H*H-2*r*(1-r)
    return R1 >= -tol and R2 >= -tol and N >= -tol


def k_interval(Gp, Gpp):
    """the set of k with G'' + k*G' > 0 as an interval (lo, hi) (either may be +-inf)"""
    if Gp > 0:
        return (-Gpp/Gp, mp.inf)
    if Gp < 0:
        return (-mp.inf, -Gpp/Gp)
    return (-mp.inf, mp.inf) if Gpp > 0 else None


print('=== 0. reproduce the lead\'s Cartesian AD values ===')
r = mp.mpf('0.375'); b1 = mp.mpf('1.05'); b2 = mp.mpf('1.05')
for face in (1, 2):
    res = V_derivs(r, b1, b2, mp.mpf(0), face)
    print(f'  face{face} at (0.375,1.05,1.05,0): G\'={mp.nstr(res[1], 13)}  '
          f'G\'\'={mp.nstr(res[2], 13)}')
print('  lead reported: face1 G\'=.110533704203 G\'\'=.424254686740 ; '
      'face2 G\'=-.114300851423 G\'\'=.432415698937')
print()

print('=== 1. legal points with the CORRECTED filters (<=200 per face) ===')
import random
random.seed(2024)
pts = {1: [], 2: []}
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
    for (rv, b1v, b2v, dv) in cand:
        if len(pts[face]) >= 200:
            break
        if not legal(rv, b1v, b2v, dv, face):
            continue
        res = V_derivs(rv, b1v, b2v, dv, face)
        if res is None:
            continue
        G, Gp, Gpp = res
        pts[face].append((rv, b1v, b2v, dv, G, Gp, Gpp))
    print(f'  face {face}: {len(pts[face])} legal points')

print()
print('=== 2. scalar k interval intersection (criterion per point) ===')
results = {}
for face in (1, 2):
    lo, hi = -mp.inf, mp.inf
    blocked = None
    sign = 1 if face == 1 else -1
    for (rv, b1v, b2v, dv, G, Gp, Gpp) in pts[face]:
        Gp_s = sign*Gp
        iv_ = k_interval(Gp_s, Gpp)
        if iv_ is None:
            blocked = (rv, b1v, b2v, dv, Gp, Gpp)
            lo, hi = None, None
            break
        lo = max(lo, iv_[0]); hi = min(hi, iv_[1])
        if lo >= hi:
            blocked = (rv, b1v, b2v, dv, Gp, Gpp)
            break
    results[face] = (lo, hi, blocked)
    if blocked:
        print(f'  face {face}: INTERSECTION EMPTY -- obstruction at '
              f'r={float(blocked[0])} b1={float(blocked[1]):.5f} '
              f'b2={float(blocked[2]):.5f} d={float(blocked[3]):.5f} '
              f'G\'={mp.nstr(blocked[4],10)} G\'\'={mp.nstr(blocked[5],10)}')
    else:
        print(f'  face {face}: k interval for the criterion = '
              f'({mp.nstr(lo,10) if lo != -mp.inf else "-inf"}, '
              f'{mp.nstr(hi,10) if hi != mp.inf else "+inf"})')

print()
print('=== 3. the combined interval over BOTH faces ===')
ok = True
lo_all, hi_all = -mp.inf, mp.inf
for face in (1, 2):
    lo, hi, blocked = results[face]
    if blocked:
        ok = False
        continue
    lo_all = max(lo_all, lo); hi_all = min(hi_all, hi)
if not ok:
    print('  cannot combine: one face has an empty intersection')
else:
    print(f'  combined k interval = '
          f'({mp.nstr(lo_all,10) if lo_all != -mp.inf else "-inf"}, '
          f'{mp.nstr(hi_all,10) if hi_all != mp.inf else "+inf"})')
    print(f'  nonempty: {lo_all < hi_all}')
    for ktest in [mp.mpf(2), mp.mpf(4), mp.mpf(6), mp.mpf(8), mp.mpf(10), mp.mpf(20)]:
        good = (lo_all < ktest < hi_all)
        print(f'     k={float(ktest)}: criterion holds on all sampled legal points? {good}')
print()
print('=== 4. the extreme values driving the interval ===')
for face in (1, 2):
    sign = 1 if face == 1 else -1
    ratios = []
    for (rv, b1v, b2v, dv, G, Gp, Gpp) in pts[face]:
        Gps = sign*Gp
        if Gps != 0:
            ratios.append((float(-Gpp/Gps), float(rv), float(b1v), float(b2v), float(dv),
                           float(Gps), float(Gpp)))
    if not ratios:
        continue
    ratios_pos = [t for t in ratios if t[5] > 0]
    ratios_neg = [t for t in ratios if t[5] < 0]
    if ratios_pos:
        m = max(ratios_pos, key=lambda t: t[0])
        print(f'  face {face}: max over G\'>0 points of (-G\'\'/G\') = {m[0]:.6f} '
              f'at r={m[1]} b1={m[2]:.5f} b2={m[3]:.5f} d={m[4]:.5f} '
              f'(G\'={m[5]:.6f} G\'\'={m[6]:.6f})  -> k must exceed this')
    if ratios_neg:
        m = min(ratios_neg, key=lambda t: t[0])
        print(f'  face {face}: min over G\'<0 points of (-G\'\'/G\') = {m[0]:.6f} '
              f'at r={m[1]} b1={m[2]:.5f} b2={m[3]:.5f} d={m[4]:.5f} '
              f'(G\'={m[5]:.6f} G\'\'={m[6]:.6f})  -> k must be below this')
