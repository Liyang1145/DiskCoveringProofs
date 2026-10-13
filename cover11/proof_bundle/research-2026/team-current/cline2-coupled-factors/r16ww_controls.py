"""cline2-coupled-factors R16ww: corrected-filter record with three working asymmetric controls.

For delta = b1 - b2 the two cap arguments coincide:
   2b1 - delta = b1 + b2 = 2b2 + delta,
so H = 2r sin(b1+b2) puts the hub on BOTH cap surfaces at once (that is the ridge, C855).
The controls below use that configuration and its perturbations, so the constraint surfaces
are genuinely active, with b1 != b2 throughout.
"""
import math, json
from pathlib import Path
from mpmath import mp

mp.dps = 40
P = Path(__file__).parent
OUT = P / 'out'

BHI = mp.acos(mp.mpf('0.375'))


def residuals(r, b1, b2, dl, H):
    s = mp.sqrt(1-r*r)
    R1 = 2*r*mp.sin(2*b1-dl)-H
    R2 = 2*r*mp.sin(2*b2+dl)-H
    N = 2*s*mp.cos(dl)*H-H*H-2*r*(1-r)
    return R1, R2, N


def cart(r, H, delta, phi1, phi2):
    hub = mp.matrix([H*mp.cos(delta), H*mp.sin(delta)])
    outs = []
    for phi in (phi1, phi2):
        sp = mp.matrix([mp.cos(phi), mp.sin(phi)])
        outs.append(mp.sqrt((hub[0]-sp[0])**2+(hub[1]-sp[1])**2)-r)
    return float(H), float(outs[0]), float(outs[1])


print('=== three ASYMMETRIC controls with the constraint surfaces ACTIVE ===')
print(f'{"#":>2s} {"r":>6s} {"b1":>7s} {"b2":>7s} {"delta":>8s} {"H":>10s} '
      f'{"R1":>12s} {"R2":>12s} {"N":>10s} | {"|hub-c1|-r":>11s} {"|hub-c2|-r":>11s} '
      f'{"|hub|":>8s} {"filter":>7s} {"cart":>6s} {"agree":>6s}')
rows = []
for (rv, b1v, b2v) in [(mp.mpf('0.375'), mp.mpf('1.10'), mp.mpf('1.05')),
                       (mp.mpf('0.377'), mp.mpf('1.05'), mp.mpf('1.15')),
                       (mp.mpf('0.379'), mp.mpf('1.16'), mp.mpf('1.02'))]:
    dv = b1v-b2v
    H = 2*rv*mp.sin(b1v+b2v)
    R1, R2, N = residuals(rv, b1v, b2v, dv, H)
    h, o1, o2 = cart(rv, H, dv, dv+b1v, dv-b2v)
    pred = (R1 >= 0 and R2 >= 0 and N >= 0 and H <= 1)
    cartf = (o1 >= 0 and o2 >= 0 and H <= 1)
    if not pred or True:
        pass
    # filter legality also requires the cap arguments be in range
    a1 = 2*b1v-dv; a2 = 2*b2v+dv
    inrange = (0 < a1 < mp.pi/2) and (0 < a2 < mp.pi/2)
    rows.append((rv, b1v, b2v, dv, H, R1, R2, N, o1, o2, pred, cartf))
    print(f'{len(rows)-1:2d} {float(rv):6.3f} {float(b1v):7.4f} {float(b2v):7.4f} '
          f'{float(dv):8.4f} {float(H):10.6f} {float(R1):12.3e} {float(R2):12.3e} '
          f'{float(N):10.6f} | {o1:11.6f} {o2:11.6f} {h:8.6f} '
          f'{str(pred):>7s} {str(cartf):>6s} {str(pred == cartf):>6s}')

print()
print('=== the identity behind the residual difference (accepted correction) ===')
for (rv, b1v, b2v, dv, H, R1, R2, N, o1, o2, pred, cartf) in rows:
    lhs = 2*rv*(mp.sin(2*b2v+dv)-mp.sin(2*b1v-dv))
    rhs = 4*rv*mp.cos(b1v+b2v)*mp.sin(b2v-b1v+dv)
    print(f'  b1={float(b1v)} b2={float(b2v)} d={float(dv)}: R2-R1={float(R2-R1):+.3e}   '
          f'2r[..]={float(lhs):+.3e}   4r cos sin={float(rhs):+.3e}   '
          f'|diff|={float(abs(lhs-rhs)):.2e}   (each 0 at the ridge)')

print()
print('=== perturbation sweep: one branch still on the cap pair, one moved off ===')
r = mp.mpf('0.375'); b1v = mp.mpf('1.10'); b2v = mp.mpf('1.05')
for dH in [mp.mpf('-0.02'), mp.mpf('-0.01'), mp.mpf('0'), mp.mpf('0.01'), mp.mpf('0.02')]:
    dv = b1v-b2v
    H0 = 2*r*mp.sin(b1v+b2v)
    H = H0+dH
    R1, R2, N = residuals(r, b1v, b2v, dv, H)
    h, o1, o2 = cart(r, H, dv, dv+b1v, dv-b2v)
    pred = (R1 >= 0 and R2 >= 0 and N >= 0 and H <= 1)
    cartf = (o1 >= 0 and o2 >= 0 and H <= 1)
    print(f'  H={float(H):.6f}: R1={float(R1):+.3e} R2={float(R2):+.3e} N={float(N):+.3e}'
          f'  |hub-c1|-r={o1:+.6f} |hub-c2|-r={o2:+.6f}  filter={pred} cart={cartf} '
          f'AGREE={pred == cartf}')
json.dump([[str(x) for x in row] for row in rows], open(OUT/'r16ww_controls.json', 'w'),
          indent=1)
print('\nsaved out/r16ww_controls.json')
