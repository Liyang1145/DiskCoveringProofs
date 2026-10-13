"""cline2-coupled-factors R16R: repaired off-face formula + bounded calibration with the
CORRECT ridge geometry.

Corrections applied (all verified in r16q_validate_e.py):
  * off-face  e2 = sqrt(Q)/(2R)  ->  e2' = (X X' + Y Y')/(2 R sqrt(Q))
    (the lead's formula; the earlier doc text wrote /(4 R sqrtQ), which is half of it --
     although the code path dQ/(2 sqrtQ)/(2R) with dQ = 2(X X'+Y Y') happens to give the
     correct value, the documented intermediate was wrong);
  * the ridge is delta = b1 - b2 with H = 2 r sin(b1+b2) (always inside [-b2,b1]);
    delta = b1 is the wedge edge;
  * the face-cap curves intersect at delta = b1 - b2, not +-(b1-b2)/2;
  * the plus norm root is j=2, the minus root j=3;
  * by the reflection (delta -> -delta, b1 <-> b2) the j=1 branch derivative is the
    NEGATIVE of the j=0 one, so a positive j=1 slope was an artefact.

This script re-derives V and dV/ddelta from the corrected formulas and reports, for
bounded calibration only: derivative values at the ridge, at the wedge edge, at the
cap-collision point, and the signs per branch, each cross-checked against finite
differences of V itself.
"""
import math, json, sys
from pathlib import Path
from mpmath import iv

iv.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
C0 = iv.mpf(f'{zJ[3]-zJ[1]:.9f}')
XX1 = iv.mpf(f'{zJ[1]-zJ[9]:.9f}')
XX2 = iv.mpf(f'{zJ[3]-zJ[9]:.9f}')
BE1 = iv.mpf(f'{-zJ[16]:.9f}'); GA1 = iv.mpf(f'{-zJ[78]:.9f}')
BE2 = iv.mpf(f'{zJ[20]:.9f}');  GA2 = iv.mpf(f'{zJ[82]:.9f}')
RR = iv.mpf(19)/50
TWO = iv.mpf(2)


def V_and_dV(r, b1, b2, dl, j):
    """V and dV/ddelta on branch j, with the CORRECTED off-face formula.
    Quad convention: quad(beta,gamma,e) = beta e^2 + gamma e (interval_joint_patch)."""
    s = iv.sqrt(1-r*r)
    A = b1-dl; B = b2+dl
    if j == 0:
        H = TWO*r*iv.sin(TWO*b1-dl); dH = -TWO*r*iv.cos(TWO*b1-dl)
    elif j == 1:
        H = TWO*r*iv.sin(TWO*b2+dl); dH = TWO*r*iv.cos(TWO*b2+dl)
    else:
        rad = (1-r)**2-s*s*iv.sin(dl)**2
        if rad.b < 0:
            return None
        sqr = iv.sqrt(rad)
        sgn = iv.mpf(1) if j == 2 else iv.mpf(-1)
        H = s*iv.cos(dl)+sgn*sqr
        dH = -s*iv.sin(dl)+sgn*(-s*s*iv.sin(dl)*iv.cos(dl)/sqr)
    V = C0*dl+H*r*(iv.sin(b1)*iv.sin(A)+iv.sin(b2)*iv.sin(B))
    dV = C0+dH*r*(iv.sin(b1)*iv.sin(A)+iv.sin(b2)*iv.sin(B)) \
        + H*r*(-iv.sin(b1)*iv.cos(A)+iv.sin(b2)*iv.cos(B))
    for i, (b, ang, dang, xx, bb, gg) in enumerate(
            [(b1, A, iv.mpf(-1), XX1, BE1, GA1), (b2, B, iv.mpf(1), XX2, BE2, GA2)]):
        if j == i:
            e = r*iv.sin(ang)/RR
            de = r*iv.cos(ang)*dang/RR
            phi = b; dphi = iv.mpf(0)
        else:
            Y = TWO*r*iv.sin(b)*iv.sin(ang)
            X = H-TWO*r*iv.sin(b)*iv.cos(ang)
            Q = X*X+Y*Y
            if Q.b < iv.mpf(1)/(50000**2):
                return None
            sq = iv.sqrt(Q)
            e = sq/(TWO*RR)
            Yp = TWO*r*iv.sin(b)*iv.cos(ang)*dang
            Xp = dH-TWO*r*iv.sin(b)*(-iv.sin(ang))*dang
            de = (X*Xp+Y*Yp)/(TWO*RR*sq)          # <- the corrected formula
            phi = iv.atan2(Y, X)
            dphi = (X*Yp-Y*Xp)/Q
        V += xx*phi+bb*e*e+gg*e
        dV += xx*dphi+(bb*TWO*e+gg)*de
    return V, dV


def fd_dV(r, b1, b2, dl, j, h=1e-11):
    p = V_and_dV(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl+h)), j)
    m = V_and_dV(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl-h)), j)
    if p is None or m is None:
        return None
    return (p[0]-m[0])/(2*iv.mpf(repr(h)))


print('=== validation: analytic dV/ddelta vs finite difference of V (corrected formula) ===')
cases = [(0.379, 1.02, 1.02, -0.45), (0.376, 1.05, 1.10, 0.10), (0.375, 1.02, 1.10, -0.30),
         (0.38, 1.05, 1.05, 0.0), (0.3795, 1.10, 1.02, -0.35)]
for (r, b1, b2, dl) in cases:
    for j in (0, 1, 2, 3):
        res = V_and_dV(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)),
                       iv.mpf(repr(dl)), j)
        fdv = fd_dV(r, b1, b2, dl, j)
        if res is None or fdv is None:
            print(f'  j={j} ({r},{b1},{b2},{dl}): not admissible / Q out of range')
            continue
        V, dV = res
        gap = float(abs(dV-fdv).b)
        print(f'  j={j} ({r},{b1},{b2},{dl}): dV={float(dV.a):+.9f} '
              f'fd={float(fdv.a):+.9f} |diff|={gap:.2e}  V={float(V.a):.9f}')

print('\n=== calibration at the three distinguished deltas ===')
print(f'{"r":>6s} {"b1":>6s} {"b2":>6s} | {"j":>2s} {"delta":>10s} {"point":>16s} '
      f'{"dV/ddelta":>12s} {"H":>10s}')
for (r, b1, b2) in [(0.375, 1.05, 1.05), (0.375, 1.10, 1.05), (0.38, 1.02, 1.10),
                    (0.378, 1.05, 1.05)]:
    marks = [('ridge b1-b2', b1-b2), ('wedge edge b1', b1), ('cap-collide', 0.5*(b1-b2))]
    for (nm, dl) in marks:
        if dl < -b2-1e-12 or dl > b1+1e-12:
            continue
        for j in (0, 1, 2, 3):
            res = V_and_dV(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)),
                           iv.mpf(repr(dl)), j)
            if res is None:
                continue
            Vr, dVr = res
            Hv = None
            try:
                if j == 0:
                    Hv = float((TWO*iv.mpf(repr(r))*iv.sin(TWO*iv.mpf(repr(b1))
                                                            - iv.mpf(repr(dl)))).a)
                elif j == 1:
                    Hv = float((TWO*iv.mpf(repr(r))*iv.sin(TWO*iv.mpf(repr(b2))
                                                            + iv.mpf(repr(dl)))).a)
            except Exception:
                pass
            print(f'{r:6.3f} {b1:6.3f} {b2:6.3f} | {j:2d} {dl:10.6f} {nm:>16s} '
                  f'{float(dVr.a):12.6f} {"" if Hv is None else f"{Hv:10.6f}"}')

print('\n=== sign structure by branch (bounded, 6x6x6 triples, 41 delta samples) ===')
import collections
sign = collections.Counter()
for i in range(6):
    r = 0.375+(0.38-0.375)*i/5
    bhi = math.acos(r)
    for a in range(6):
        b1 = 1+(bhi-1)*a/5
        for c in range(6):
            b2 = 1+(bhi-1)*c/5
            for m in range(41):
                dl = -b2+(b1+b2)*m/40
                for j in (0, 1, 2, 3):
                    res = V_and_dV(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)),
                                   iv.mpf(repr(dl)), j)
                    if res is None:
                        continue
                    d = float(res[1].a)
                    sign[(j, 'pos' if d > 0 else ('neg' if d < 0 else 'zero'))] += 1
for k in sorted(sign, key=str):
    print(f'   j={k[0]} {k[1]:4s}: {sign[k]}')
