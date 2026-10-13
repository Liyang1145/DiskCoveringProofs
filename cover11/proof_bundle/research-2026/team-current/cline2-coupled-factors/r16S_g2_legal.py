"""cline2-coupled-factors R16S: second derivative of the hub objective on the LEGAL face arcs.

Corrected first derivative (lead + r16q validation):
    V(delta) = (z3-z1) delta + H r (sin b1 sin A + sin b2 sin B)
               + a1 phi1 + beta1 e1^2 + gamma1 e1
               + a2 phi2 + beta2 e2^2 + gamma2 e2
    A = b1-delta, B = b2+delta, H = 2r sin(2b1-delta) on face 1
    e2 = sqrt(Q)/(2R),  e2' = (X X' + Y Y')/(2 R sqrt(Q))
with  X = H - 2r sin b2 cos B,  Y = 2r sin b2 sin B,
      X' = H' + 2r sin b2 sin B, Y' = 2r sin b2 cos B,
      X'' = H'' + 2r sin b2 cos B, Y'' = -2r sin b2 sin B,  H'' = -H   (on face 1).

G'' = d2V/ddelta2 collects:
  on-face-1 : (2 beta1 e1 + gamma1) e1'' + 2 beta1 (e1')^2      with e1'' = -r sinA/R
  off-face-2: (2 beta2 e2 + gamma2) e2'' + 2 beta2 (e2')^2 + 2 a2 phi2'
  hub       : H'' k + 2 H' k' + H k''
with e2' = Q'/(4 R sqrtQ), e2'' = Q''/(4 R sqrtQ) - Q'^2/(8 R Q^{3/2}),
     Q'' = 2(X'^2 + X X'' + Y'^2 + Y Y'').

LEGAL points only: the feasibility filters
    (F1) H <= 2 r sin(2 b2 + delta)      (inside the face-2 cap)
    (F2) H^2 - 2 s cos(delta) H + 2 r (1-r) <= 0   (inside the norm circle)
    (F3) H <= 2 r sin(2 b1 - delta)      (inside the face-1 cap; identity on j=0)
and delta in [-b2, b1], plus the Q-range guard.  My earlier r16r sign census had NO filters,
so its counts are not legal.
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
XX1 = iv.mpf(f'{zJ[1]-zJ[9]:.9f}'); XX2 = iv.mpf(f'{zJ[3]-zJ[9]:.9f}')
BE1 = iv.mpf(f'{-zJ[16]:.9f}'); GA1 = iv.mpf(f'{-zJ[78]:.9f}')
BE2 = iv.mpf(f'{zJ[20]:.9f}');  GA2 = iv.mpf(f'{zJ[82]:.9f}')
RR = iv.mpf(19)/50
TWO = iv.mpf(2); ZERO = iv.mpf(0); ONE = iv.mpf(1)


def face1_data(r, b1, b2, dl):
    """all first/second delta-derivatives on the face-1 arc, as exact expressions"""
    s = iv.sqrt(1-r*r)
    A = b1-dl; B = b2+dl
    sinA, cosA = iv.sin(A), iv.cos(A)
    sinB, cosB = iv.sin(B), iv.cos(B)
    sb1, cb1 = iv.sin(b1), iv.cos(b1)
    sb2, cb2 = iv.sin(b2), iv.cos(b2)
    H = TWO*r*iv.sin(TWO*b1-dl)
    Hp = -TWO*r*iv.cos(TWO*b1-dl)
    Hpp = -H
    # hub term:  k = r(sb1 sinA + sb2 sinB); ki = i-th delta-derivative of k
    k0 = r*(sb1*sinA+sb2*sinB)
    k1 = r*(-sb1*cosA+sb2*cosB)
    k2 = r*(-sb1*sinA+sb2*sinB)*(-1)
    k2 = -r*(sb1*sinA+sb2*sinB)
    hub2 = Hpp*k0+TWO*Hp*k1+H*k2
    # on-face 1
    e1 = r*sinA/RR; e1p = -r*cosA/RR; e1pp = -r*sinA/RR
    on2 = (TWO*BE1*e1+GA1)*e1pp+TWO*BE1*e1p*e1p
    # off-face 2
    Y = TWO*r*sb2*sinB
    X = H-TWO*r*sb2*cosB
    Yp = TWO*r*sb2*cosB
    Xp = Hp+TWO*r*sb2*sinB
    Ypp = -TWO*r*sb2*sinB
    Xpp = Hpp+TWO*r*sb2*cosB
    Q = X*X+Y*Y
    if Q.b < iv.mpf(1)/(50000**2):
        return None
    sq = iv.sqrt(Q)
    Qp = TWO*(X*Xp+Y*Yp)
    Qpp = TWO*(Xp*Xp+X*Xpp+Yp*Yp+Y*Ypp)
    e2 = sq/(TWO*RR)
    e2p = Qp/(TWO*sq)/(TWO*RR)                     # = (X X'+Y Y')/(2 R sqrtQ)
    e2pp = Qpp/(TWO*sq)/(TWO*RR)-Qp*Qp/(4*sq**3)/(TWO*RR)
    phi2p = (X*Yp-Y*Xp)/Q
    off2 = (TWO*BE2*e2+GA2)*e2pp+TWO*BE2*e2p*e2p+TWO*XX2*phi2p
    G = C0+H*k1+Hp*k0+XX1*ZERO+BE1*e1*e1+GA1*e1+XX2*iv.atan2(Y, X)+BE2*e2*e2+GA2*e2
    Gp = C0+Hp*k1+H*k2+Hpp*k0+Hp*k1 \
        + BE1*TWO*e1*e1p+GA1*e1p \
        + XX2*phi2p+BE2*TWO*e2*e2p+GA2*e2p
    Gpp = hub2+on2+off2
    return dict(A=A, B=B, H=H, Hp=Hp, Hpp=Hpp, k0=k0, k1=k1, k2=k2,
                e1=e1, e1p=e1p, e1pp=e1pp, e2=e2, e2p=e2p, e2pp=e2pp,
                phi2=iv.atan2(Y, X), phi2p=phi2p, X=X, Y=Y, Q=Q, s=s,
                G=G, G1=Gp, G2=Gpp)


def legal(r, b1, b2, dl, tol=0.0):
    """the legality filters; returns (flag, reason)"""
    q = face1_data(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl)))
    if q is None:
        return False, 'Q-range'
    H = float(q['H'].a)
    s = float(q['s'].a)
    cap1 = 2*r*math.sin(2*b1-dl)
    cap2 = 2*r*math.sin(2*b2+dl)
    beta = H*H-2*s*math.cos(dl)*H+2*r*(1-r)
    if H > cap1+tol:
        return False, 'outside cap1'
    if H > cap2+tol:
        return False, 'outside cap2'
    if beta > tol:
        return False, 'outside norm circle'
    if H <= 0:
        return False, 'H<=0'
    return True, 'legal'


print('=== 1. validate G1 and G2 against finite differences of V (legal points) ===')


def V_of(r, b1, b2, dl):
    q = face1_data(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl)))
    return None if q is None else q['G']


print(f'{"r":>6s} {"b1":>6s} {"b2":>6s} {"dl":>8s} {"G1 analytic":>14s} {"G1 FD":>14s} '
      f'{"G2 analytic":>14s} {"G2 FD":>14s} {"legal":>6s}')
val_rows = []
for (r, b1, b2, dl) in [(0.379, 1.02, 1.02, -0.45), (0.376, 1.05, 1.10, 0.10),
                        (0.3795, 1.10, 1.05, -0.20), (0.375, 1.05, 1.05, 0.0),
                        (0.38, 1.10, 1.02, -0.35)]:
    ok, why = legal(r, b1, b2, dl)
    h = 1e-5
    vp = V_of(r, b1, b2, dl+h); vm = V_of(r, b1, b2, dl-h)
    v0 = V_of(r, b1, b2, dl)
    if vp is None or vm is None or v0 is None:
        continue
    fd1 = (vp-vm)/(2*iv.mpf(repr(h)))
    fd2 = (vp-2*v0+vm)/iv.mpf(repr(h))**2
    q = face1_data(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl)))
    print(f'{r:6.3f} {b1:6.3f} {b2:6.3f} {dl:8.4f} {float(q["G1"].a):14.9f} '
          f'{float(fd1.a):14.9f} {float(q["G2"].a):14.9f} {float(fd2.a):14.9f} '
          f'{("yes" if ok else "no"):>6s}')
    val_rows.append((r, b1, b2, dl, float(q["G1"].a), float(fd1.a),
                     float(q["G2"].a), float(fd2.a), ok))

print('\n=== 2. LEGAL-point scan (<=200 points) on the face-1 arc ===')
legals = []
rng = []
for i in range(6):
    r = 0.375+(0.38-0.375)*i/5
    bhi = math.acos(r)
    for a in range(6):
        b1 = 1+(bhi-1)*a/5
        for b in range(6):
            b2 = 1+(bhi-1)*b/5
            for m in range(11):
                dl = -b2+(b1+b2)*m/10
                rng.append((r, b1, b2, dl))
import random
random.seed(1609)
random.shuffle(rng)
for (r, b1, b2, dl) in rng:
    if len(legals) >= 200:
        break
    ok, why = legal(r, b1, b2, dl)
    if not ok:
        continue
    q = face1_data(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl)))
    legals.append((r, b1, b2, dl, float(q['G'].a), float(q['G1'].a), float(q['G2'].a)))
print(f'legal points collected: {len(legals)} of {len(rng)} candidates')
if legals:
    g2 = [row[6] for row in legals]
    g1 = [row[5] for row in legals]
    print(f'G  range over legal points: [{min(row[4] for row in legals):.6f}, '
          f'{max(row[4] for row in legals):.6f}]')
    print(f'G\' range : [{min(g1):.6f}, {max(g1):.6f}]   '
          f'(#negative {sum(1 for v in g1 if v < 0)}, #positive {sum(1 for v in g1 if v > 0)})')
    print(f'G\'\' range: [{min(g2):.6f}, {max(g2):.6f}]   '
          f'(#negative {sum(1 for v in g2 if v < 0)}, #positive {sum(1 for v in g2 if v > 0)})')
    worst = min(legals, key=lambda t: t[6])
    best = max(legals, key=lambda t: t[6])
    print(f'\nstrongest NEGATIVE G\'\' witness: {worst[6]:.9f} at '
          f'r={worst[0]} b1={worst[1]:.6f} b2={worst[2]:.6f} d={worst[3]:.6f} '
          f'(G={worst[4]:.6f}, G\'={worst[5]:.6f})')
    print(f'strongest POSITIVE G\'\' witness: {best[6]:.9f} at '
          f'r={best[0]} b1={best[1]:.6f} b2={best[2]:.6f} d={best[3]:.6f} '
          f'(G={best[4]:.6f}, G\'={best[5]:.6f})')
    neg = [row for row in legals if row[6] < 0]
    print(f'\nlegal points with G\'\' < 0 : {len(neg)} of {len(legals)}'
          + ('  -> NOT convex on the legal face-1 arc' if neg else '  -> convexity consistent'))
    # any interior stationary point?
    stat = [row for row in legals if abs(row[5]) < 0.05]
    print(f'legal points with |G\'| < 0.05: {len(stat)}')
    for row in stat[:6]:
        print(f'   r={row[0]} b1={row[1]:.6f} b2={row[2]:.6f} d={row[3]:.6f} '
              f'G\'={row[5]:+.6f} G\'\'={row[6]:+.6f}')
json.dump({'validation': val_rows, 'legal': legals}, open(OUT/'r16s_legal.json', 'w'),
          indent=1)
print('\nsaved out/r16s_legal.json')
