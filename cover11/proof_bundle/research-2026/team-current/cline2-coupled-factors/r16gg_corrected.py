"""cline2-coupled-factors R16gg: the corrected second derivative and whether the legal-arc
conclusions survive.

BUG: in face1_data (r16S_g2_legal.py:81) the off-face contribution used
     off2 = (2 beta2 e2 + gamma2) e2'' + 2 beta2 (e2')^2 + 2 a2 phi2'
but the third term of d2V/ddelta2 is  a2 * phi2''  (no factor 2, and phi2'' not phi2').
Verified three ways at r=.375, b1=b2=1.05, delta=0:
   module G''                     = 0.36640683394183493
   hub2 + on2 + [corrected off2]  = 0.4242546867396482
   high-precision second difference of V = 0.4242546867...
The 0.0578 gap is exactly 2 a2 phi2' + a2 phi2''... computed below.
"""
import math, json, sys
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
R = mp.mpf(19)/50
C0 = mp.mpf(f'{zJ[3]-zJ[1]:.9f}')
XX1 = mp.mpf(f'{zJ[1]-zJ[9]:.9f}'); XX2 = mp.mpf(f'{zJ[3]-zJ[9]:.9f}')
BE1 = mp.mpf(f'{-zJ[16]:.9f}'); GA1 = mp.mpf(f'{-zJ[78]:.9f}')
BE2 = mp.mpf(f'{zJ[20]:.9f}');  GA2 = mp.mpf(f'{zJ[82]:.9f}')


def corrected(r, b1, b2, dl, face=1):
    """returns (G, G', G'') for the given face arc, with the CORRECT second derivative"""
    r = mp.mpf(repr(r)); b1 = mp.mpf(repr(b1)); b2 = mp.mpf(repr(b2)); dl = mp.mpf(repr(dl))
    A = b1-dl; B = b2+dl
    if face == 1:
        H = 2*r*mp.sin(2*b1-dl); Hp = -2*r*mp.cos(2*b1-dl)
    else:
        H = 2*r*mp.sin(2*b2+dl); Hp = 2*r*mp.cos(2*b2+dl)
    Hpp = -H
    k = r*(mp.sin(b1)*mp.sin(A)+mp.sin(b2)*mp.sin(B))
    kp = r*(-mp.sin(b1)*mp.cos(A)+mp.sin(b2)*mp.cos(B))
    kpp = -r*(mp.sin(b1)*mp.sin(A)+mp.sin(b2)*mp.sin(B))
    G = C0*dl+H*k
    G1 = C0+Hp*k+H*kp
    G2 = Hpp*k+2*Hp*kp+H*kpp
    for i, (b, ang, dang, xx, bb, gg) in enumerate(
            [(b1, A, -1, XX1, BE1, GA1), (b2, B, 1, XX2, BE2, GA2)]):
        on_this = (face == 1 and i == 0) or (face == 2 and i == 1)
        if on_this:
            e = r*mp.sin(ang)/R; ep = r*mp.cos(ang)*dang/R
            epp = -r*mp.sin(ang)/R
            phi = b; phip = mp.mpf(0); phipp = mp.mpf(0)
        else:
            Y = 2*r*mp.sin(b)*mp.sin(ang)
            X = H-2*r*mp.sin(b)*mp.cos(ang)
            Yp = 2*r*mp.sin(b)*mp.cos(ang)*dang
            Xp = Hp-2*r*mp.sin(b)*(-mp.sin(ang))*dang
            Ypp = -2*r*mp.sin(b)*mp.sin(ang)*dang*dang
            Xpp = Hpp-2*r*mp.sin(b)*(-mp.cos(ang))*dang*dang
            Q = X*X+Y*Y
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
        G1 += xx*phip+(2*bb*e+gg)*ep
        G2 += xx*phipp+(2*bb*e+gg)*epp+2*bb*ep*ep
    return float(G), float(G1), float(G2)


print('=== bug confirmation at the reference point ===')
print('  corrected G\'\' =', corrected(0.375, 1.05, 1.05, 0.0, 1)[2])
print('  module   G\'\'  = 0.36640683394183493')
print('  FD of V       = 0.4242546866478459')
print('  gap           =', corrected(0.375, 1.05, 1.05, 0.0, 1)[2]-0.36640683394183493)
print()
print('=== legal-arc scan with the CORRECTED G\'\' (<=200 legal points per face) ===')
import random


def legal(r, b1, b2, dl, face):
    A = b1-dl; B = b2+dl
    s = math.sqrt(1-r*r)
    H = 2*r*math.sin(2*b1-dl) if face == 1 else 2*r*math.sin(2*b2+dl)
    cap1 = 2*r*math.sin(2*b1-dl); cap2 = 2*r*math.sin(2*b2+dl)
    beta = H*H-2*s*math.cos(dl)*H+2*r*(1-r)
    return H > 0 and H <= cap1+0 and H <= cap2+0 and beta <= 0


for face in (1, 2):
    cand = []
    for i in range(6):
        r = 0.375+(0.38-0.375)*i/5
        bhi = math.acos(r)
        for a in range(6):
            b1 = 1+(bhi-1)*a/5
            for c in range(6):
                b2 = 1+(bhi-1)*c/5
                for m in range(11):
                    cand.append((r, b1, b2, -b2+(b1+b2)*m/10))
    random.seed(1700+face)
    random.shuffle(cand)
    pts = []
    for (r, b1, b2, dl) in cand:
        if len(pts) >= 200:
            break
        if not legal(r, b1, b2, dl, face):
            continue
        G, G1, G2 = corrected(r, b1, b2, dl, face)
        pts.append((r, b1, b2, dl, G, G1, G2))
    g1 = [p[5] for p in pts]; g2 = [p[6] for p in pts]
    print(f'face {face}: {len(pts)} legal points')
    print(f"   G'  in [{min(g1):+.6f}, {max(g1):+.6f}]  (#neg {sum(1 for v in g1 if v<0)}"
          f" / #pos {sum(1 for v in g1 if v>0)})")
    print(f"   G'' in [{min(g2):+.6f}, {max(g2):+.6f}]  (#neg {sum(1 for v in g2 if v<0)}"
          f" / #pos {sum(1 for v in g2 if v>0)})")
    w = min(pts, key=lambda t: t[6]); b_ = max(pts, key=lambda t: t[6])
    print(f"   strongest negative G'' = {w[6]:+.9f} at r={w[0]} b1={w[1]:.6f} b2={w[2]:.6f}"
          f" d={w[3]:.6f}  (G'={w[5]:+.6f})")
    print(f"   strongest positive G'' = {b_[6]:+.9f} at r={b_[0]} b1={b_[1]:.6f}"
          f" b2={b_[2]:.6f} d={b_[3]:.6f}  (G'={b_[5]:+.6f})")
    neg = [p for p in pts if p[6] < 0]
    print(f"   -> {'NOT convex' if neg else 'convex-consistent'} on this legal arc")
    print()
