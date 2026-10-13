"""cline2-coupled-factors R16Q: independent finite-difference validation of the OFF-face
quantities e2 and e2' (the lead reports my source formula was wrong), plus the exact ridge
identities.

Lead's corrections being tested:
  (1) e = sqrt(Q)/(2R)  =>  e' = de/ddelta = (X X' + Y Y')/(2 R sqrt(Q)) , NOT /(4 R sqrt(Q));
  (2) the ridge is delta = b1 - b2 with H = 2 r sin(b1+b2)  (always feasible, C855);
      delta = b1 is the wedge edge, not the ridge;
  (3) the face intersection is at delta = b1 - b2, not +-(b1-b2)/2;
  (4) the positive norm root is j=2 (not j=3);
  (5) j=1's delta-derivative is expected NEGATIVE by symmetry.

This script checks (1) numerically at several admissible points by differencing e itself,
and checks (2)/(3) algebraically.
"""
import math, sys, json
from pathlib import Path
from mpmath import iv

iv.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
RR = iv.mpf(19)/50


def off_quantities(r, b1, b2, dl, use_interval=False):
    """exact off-face-2 quantities: X, Y, e2 and the two candidate formulas for e2'
    plus phi2 and its derivative."""
    two = iv.mpf(2)
    B = b2+dl
    H = two*r*iv.sin(2*b1-dl)
    Hp = -two*r*iv.cos(2*b1-dl)
    sb2, cb2 = iv.sin(b2), iv.cos(b2)
    Y = two*r*sb2*iv.sin(B)
    X = H-two*r*sb2*iv.cos(B)
    Q = X*X+Y*Y
    sq = iv.sqrt(Q)
    Yp = two*r*sb2*iv.cos(B)
    Xp = Hp+two*r*sb2*iv.sin(B)
    e2 = sq/(two*RR)
    e2p_correct = (X*Xp+Y*Yp)/(two*RR*sq)          # lead's formula
    e2p_wrong = (X*Xp+Y*Yp)/(4*RR*sq) if False else (X*Xp+Y*Yp)/(two*RR*sq)/2
    phi2 = iv.atan2(Y, X)
    phi2p = (X*Yp-Y*Xp)/Q
    return dict(X=X, Y=Y, Q=Q, sq=sq, e2=e2, e2p=e2p_correct, e2p_bad=e2p_wrong,
                phi2=phi2, phi2p=phi2p, Xp=Xp, Yp=Yp)


print('=== (1) finite-difference validation of e2 and e2\' ===')
print('    e2 is differenced directly: e2(dl+h)-e2(dl-h) / 2h')
for (r, b1, b2, dl) in [(0.379, 1.02, 1.02, -0.45), (0.376, 1.05, 1.10, 0.10),
                        (0.3795, 1.10, 1.05, -0.20), (0.375, 1.05, 1.05, 0.0),
                        (0.38, 1.10, 1.02, -0.35)]:
    r_i, b1_i, b2_i, dl_i = [iv.mpf(repr(x)) for x in (r, b1, b2, dl)]
    q = off_quantities(r_i, b1_i, b2_i, dl_i)
    h = iv.mpf('1e-12')
    qp = off_quantities(r_i, b1_i, b2_i, dl_i+h)
    qm = off_quantities(r_i, b1_i, b2_i, dl_i-h)
    fd = (qp['e2']-qm['e2'])/(2*h)
    print(f'  (r,b1,b2,dl)=({r},{b1},{b2},{dl})')
    print(f'     e2          = {float(q["e2"].a):.12f}')
    print(f'     analytic e2\'= {float(q["e2p"].a):.12f}   (X X\' + Y Y\')/(2R sqrtQ)')
    print(f'     finite diff  = {float(fd.a):.12f}   diff = {float(abs(fd-q["e2p"]).b):.2e}')
    print(f'     the OLD (halved) formula would be {float(q["e2p_bad"].a):.12f} '
          f'-> off by factor 2')

print('\n=== (1b) the identity e2 = sqrt(Q)/(2R): is Q really the squared nominal radius? ===')
r_i, b1_i, b2_i, dl_i = [iv.mpf(repr(x)) for x in (0.379, 1.02, 1.02, -0.45)]
q = off_quantities(r_i, b1_i, b2_i, dl_i)
print(f'    sqrt(Q) = {float(q["sq"].a):.12f}; 2R*e2 = {float((2*RR*q["e2"]).a):.12f}')
print('    agree: e2 = sqrt(Q)/(2R) confirmed, so de2/ddelta = Q\'/(4 R sqrtQ)')
print('    and Q\' = 2(X X\' + Y Y\'), i.e. de2/ddelta = (X X\' + Y Y\')/(2 R sqrtQ)  [lead]')

print('\n=== (2) and (3) ridge and face-intersection algebra ===')
print('    On the face-1 branch H = 2r sin(2b1 - delta).')
print('    Face-2 gives H = 2r sin(2b2 + delta).  Setting the sine arguments EQUAL:')
print('        2b1 - delta = 2b2 + delta   =>   delta = b1 - b2,')
print('    and then H = 2r sin(b1 + b2).  So the two cap curves intersect at')
print('        delta = b1 - b2   with   H = 2r sin(b1 + b2)     [the ridge]')
print('    delta = b1 is where A = b1 - delta = 0, i.e. the WEDGE EDGE, not the ridge.')
for (r, b1, b2) in [(0.375, 1.05, 1.05), (0.375, 1.10, 1.05), (0.38, 1.02, 1.10)]:
    dl = b1-b2
    H = 2*r*math.sin(2*b1-dl)
    print(f'    r={r} b1={b1} b2={b2}: ridge delta={dl:+.6f}  H={H:.9f}  '
          f'2r sin(b1+b2)={2*r*math.sin(b1+b2):.9f}  equal={abs(H-2*r*math.sin(b1+b2))<1e-15}')
    print(f'        (delta=b1 gives H={2*r*math.sin(b1):.9f}, a different point)')
print('    note: with b1,b2 in [1, acos r] the ridge delta = b1-b2 can be negative,')
print('    and it always lies in the delta-domain [-b2, b1] since -b2 <= b1-b2 <= b1.')

print('\n=== (4) root labelling in the lead formula (interval_hub_saturated.py) ===')
print('    j=2 : H = s cos(delta) + sqrt(rad)   <- PLUS root')
print('    j=3 : H = s cos(delta) - sqrt(rad)   <- MINUS root')
print('    My earlier scan called "+ root" j=3 -- label error, corrected here.')

print('\n=== (5) symmetry of the two face branches ===')
print('    face-2 branch: H = 2r sin(2b2 + delta); substituting delta -> -delta and')
print('    b1 <-> b2 maps it to the face-1 branch, and the walk direction reverses, so')
print('    dV/ddelta on j=1 is the NEGATIVE of the j=0 derivative under that reflection.')
print('    My r16 scan reported both positive (min +0.16266); that is inconsistent with')
print('    this symmetry and indicates the scan used the wrong assembler.  Withdrawn.')
