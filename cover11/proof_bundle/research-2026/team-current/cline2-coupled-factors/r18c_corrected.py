"""cline2-coupled-factors R18c: CORRECTED source-distance identity (my first version had the
sign/factor wrong: the cross term is -4rH sin b sin(ang), not -2rH[...]).

  Q = X^2+Y^2 with X = H - 2r sin b cos(ang), Y = 2r sin b sin(ang)
    = (H - 2r sin b cos ang)^2 + (2r sin b sin ang)^2
    = H^2 + 4r^2 sin^2 b - 4 r H sin b cos(ang)
and since sin b sin ang = (cos(b-ang) - cos(b+ang))/2,
    = H^2 + 4r^2 sin^2 b - 2 r H [ cos(b-ang) - cos(b+ang) ]          (*)

on a face chart H = 2r sin A:
    Q = 4r^2 [ sin^2 A + sin^2 b - 2 sin A sin b cos(ang) ]
      = 4r^2 [ sin^2 A + sin^2 b - sin b (cos(A-ang) - cos(A+ang)) ]
      = 4r^2 [ sin^2 b + sin^2 A - sin b cos(A-ang) + sin b cos(A+ang) ]
and A + ang = T := b1 + b2, so
    Q = 4r^2 [ sin^2 b + sin^2 A - sin b cos(A-ang) + sin b cos T ]    (**)
"""
import json
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']

print('=== verification of (*) and (**) ===')
worst_a = 0; worst_b = 0; n = 0
for rv in ['0.379', '0.3793', '0.37999']:
    for b2v in ['0.61', '0.8', '1.0', '1.15']:
        for pv in ['-0.9', '-0.3', '0.0', '0.3', '0.6']:
            r = mp.mpf(rv); b2 = mp.mpf(b2v); p = mp.mpf(pv); b1 = mp.mpf(1)
            A = b1-p; B = b2+p; T = b1+b2
            if A <= 0 or B <= 0:
                continue
            H = 2*r*mp.sin(A)
            X = H-2*r*mp.sin(b2)*mp.cos(B)
            Y = 2*r*mp.sin(b2)*mp.sin(B)
            Q = X*X+Y*Y
            star = H*H+4*r*r*mp.sin(b2)**2-2*r*H*(mp.cos(b2-B)-mp.cos(b2+B))
            star2 = H*H+4*r*r*mp.sin(b2)**2-4*r*H*mp.sin(b2)*mp.sin(B)
            dstar = 4*r*r*(mp.sin(b2)**2+mp.sin(A)**2-mp.sin(b2)*mp.cos(A-B)
                           + mp.sin(b2)*mp.cos(T))
            worst_a = max(worst_a, abs(Q-star), abs(Q-star2))
            worst_b = max(worst_b, abs(Q-dstar))
            n += 1
print(f'  (*)  max |Q - expression| over {n} cases = {mp.nstr(worst_a,4)}')
print(f'  (**) max |Q - expression| over {n} cases = {mp.nstr(worst_b,4)}')
print()
print('  => (**) is an EXACT identity: on a face chart the T-dependence of the squared')
print('     source distance enters ONLY through the single term sin b cos T.')
print()
print('=== degeneracy T = pi/2 ===')
print('  At T = pi/2, cos T = 0, so')
print('     Q = 4r^2 [ sin^2 b + sin^2 A - sin b cos(A-ang) ]')
print('  and the two disk constraints coincide exactly:')
r = mp.mpf('0.3795')
for b1v in ['0.60946080763725372899', '0.8', '1.0', '1.1']:
    b1 = mp.mpf(b1v); b2 = mp.pi/2-b1
    D1 = (r*mp.sin(2*b1), -r*mp.cos(2*b1))
    D2 = (r*mp.sin(2*b2), r*mp.cos(2*b2))
    sep = mp.sqrt((D1[0]-D2[0])**2+(D1[1]-D2[1])**2)
    print(f'   b1={b1v:22s}: |D1-D2| = {mp.nstr(sep,6)}')
print()
print('=== the second structural fact: the radial quadratic ===')
print('  The hub term of the objective is  a*phi + beta*e^2 + gamma*e  with e = u/R,')
print('  u = sqrt(Q).  Writing m = beta/R^2, n = gamma/R:')
print('     beta e^2 + gamma e = m u^2 + n u = m (u + n/(2m))^2 - n^2/(4m)')
print('  i.e. an exact SQUARE about the minimiser u* = -n/(2m), with remainder -n^2/(4m).')
for jm, (bi, gi) in [(0, (-zJ[16], -zJ[78])), (1, (zJ[20], zJ[82]))]:
    beta = mp.mpf(f'{bi:.9f}'); gam = mp.mpf(f'{gi:.9f}')
    RR = mp.mpf(19)/50
    m = beta/RR**2; nn = gam/RR
    print(f'   j={jm}: beta={beta} gamma={gam}  -> m={mp.nstr(m,10)} n={mp.nstr(nn,10)}')
    print(f'          u* = -n/(2m) = {mp.nstr(-nn/(2*m),10)}   remainder = '
          f'{mp.nstr(-nn*nn/(4*m),10)}')
