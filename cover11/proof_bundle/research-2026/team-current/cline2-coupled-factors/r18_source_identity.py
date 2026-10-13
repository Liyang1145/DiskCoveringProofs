"""cline2-coupled-factors R18: degeneracy test T = b1+b2 = pi/2, and the source-distance
identity that removes the near-source cancellation.

Objects (lead/allbearing_boundary_jet.py):
  face charts j=0,1:  A = b1-p, B = b2+p, H = 2r sin(2b1-p) (j=0) / 2r sin(2b2+p) (j=1)
      off-face source:  X = H - 2r sin(b) cos(ang),  Y = 2r sin(b) sin(ang)
      e = sqrt(X^2+Y^2)/(2R),  phi = atan2(Y,X)
  norm chart j=2:  v = s + (1-r) cos p, t = (1-r) sin p, s = sqrt(1-r^2)
      X = v - r sin(2b),  Y = 2r sin^2 b - t   (sg = -1 for b1)
      1-p (face charts) corresponds to chi := (v - s)/(1-r) = cos p
"""
import json, math
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
Z = {i: mp.mpf(f'{zJ[i]:.9f}') for i in range(len(zJ))}
R = mp.mpf(19)/50


def face_source(r, b1, b2, p, j):
    """the off-face source data on face chart j (the other face is the 'source')"""
    if j == 0:
        A = b1-p; B = b2+p; H = 2*r*mp.sin(2*b1-p)
        b, ang, sg = b2, B, mp.mpf(1)
    else:
        A = b1-p; B = b2+p; H = 2*r*mp.sin(2*b2+p)
        b, ang, sg = b1, A, mp.mpf(-1)
    X = H-2*r*mp.sin(b)*mp.cos(ang)
    Y = 2*r*mp.sin(b)*mp.sin(ang)
    Q = X*X+Y*Y
    return dict(A=A, B=B, H=H, X=X, Y=Y, Q=Q, b=b, ang=ang)


print('=== 0. verify the source-distance identity Q = H^2 + 4r^2 sin^2 b - 4rH sin b sin(ang)')
print('       and its product-to-sum form')
print('       Q = H^2 + 4r^2 sin^2 b - 2rH[cos(b-ang) - cos(b+ang)]')
worst = 0
cases = []
for rv in ['0.379', '0.3793', '0.37999']:
    for b2v in ['0.61', '0.8', '1.0']:
        for pv in ['-0.9', '-0.3', '0.0', '0.3']:
            r = mp.mpf(rv); b2 = mp.mpf(b2v); p = mp.mpf(pv)
            b1 = mp.mpf(1)
            A = b1-p; B = b2+p
            if A <= 0 or B <= 0:
                continue
            D = face_source(r, b1, b2, p, 0)
            H = D['H']; b = D['b']; ang = D['ang']
            Q1 = D['Q']
            Q2 = H*H+4*r*r*mp.sin(b)**2-4*r*H*mp.sin(b)*mp.sin(ang)
            Q3 = H*H+4*r*r*mp.sin(b)**2-2*r*H*(mp.cos(b-ang)-mp.cos(b+ang))
            worst = max(worst, abs(Q1-Q2), abs(Q1-Q3))
            cases.append((rv, b2v, pv, float(Q1)))
print(f'  max |Q - identity| over {len(cases)} cases = {mp.nstr(worst,4)}')
print()
print('  IMPORTANT: with H = 2r sin(2b1-p) on face 1, the product-to-sum form collapses')
print('  to a pure difference of cosines:')
print('     Q = 4r^2[ (cos(b-ang) - cos(b+ang))/4 + sin^2 b - (1/2) sin(b+ang)... ]')
print('  Checking the cleaner equivalent: Q = 4r^2( sin b cos ang )^2 - 4r^2 sin b cos ang')
print('          *2(sin... ) -- rather, verify Q = (H-2r sin b cos ang)^2 + (2r sin b sin ang)^2')
for idx in (0, min(3, len(cases)-1)):
    rv, b2v, pv, Qv = cases[idx]
    r = mp.mpf(rv); b2 = mp.mpf(b2v); p = mp.mpf(pv); b1 = mp.mpf(1)
    D = face_source(r, b1, b2, p, 0)
    print(f'  r={rv} b2={b2v} p={pv}: Q={Qv:.10f}  det={float(D["Q"]):.10f}')
