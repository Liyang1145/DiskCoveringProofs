"""cline2-coupled-factors R18e: the CORRECT source-distance identity.

On a face chart the hub sits at polar (H, p) with H = 2r sin(2b_l - p) for the
on-face bearing b_l (l = 1 for j=0, l = 2 for j=1); the off-face source is the site
direction (sin b_o, -cos b_o) for j=0 and (sin b_o, +cos b_o) for j=1.

  Q = |hub - source|^2 = H^2 + 1 - 2 H [ sin b_o cos p + sg cos b_o sin p ]

With H = 2r sin(2b_l - p) and the double-angle collapse this becomes, exactly,

  Q = 1 - 4 r sin(2 b_o) + 2 r^2 [ 1 - cos(4 b_l - 2p) ]                     (*)

so the ENTIRE dependence on the on-face bearing is through the single angle
(4 b_l - 2p).  This is the exact representation that removes the near-source
cancellation in X = H - 2r sin b_o cos(ang), Y = 2r sin b_o sin(ang).
"""
import json
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']


def Q_code(r, b1, b2, p, j):
    if j == 0:
        A = b1-p; B = b2+p; H = 2*r*mp.sin(2*b1-p)
        b, ang = b2, B
    else:
        A = b1-p; B = b2+p; H = 2*r*mp.sin(2*b2+p)
        b, ang = b1, A
    X = H-2*r*mp.sin(b)*mp.cos(ang)
    Y = 2*r*mp.sin(b)*mp.sin(ang)
    return X*X+Y*Y, H


print('=== verification: Q versus 1 - 4r sin(2 b_o) + 2r^2[1 - cos(4 b_l - 2p)] ===')
worst = 0; n = 0
for j in (0, 1):
    for rv in ['0.379', '0.3793', '0.37999']:
        for o in ['0.61', '0.8', '1.0', '1.15']:
            for pv in ['-0.9', '-0.5', '0.0', '0.4', '0.8']:
                r = mp.mpf(rv); p = mp.mpf(pv)
                if j == 0:
                    b1 = mp.mpf('1.0'); b2 = mp.mpf(o); bl = b1; bo = b2
                else:
                    b1 = mp.mpf(o); b2 = mp.mpf('1.0'); bl = b2; bo = b1
                Q, H = Q_code(r, b1, b2, p, j)
                cand = (1-4*r*mp.sin(2*bo)+2*r*r*(1-mp.cos(4*bl-2*p)))
                worst = max(worst, abs(Q-cand)); n += 1
print(f'  max |Q - closed form| over {n} cases = {mp.nstr(worst,4)}')
print()

print('=== structural consequences ===')
print('  (i) Q is AFFINE in sin(2 b_o) and depends on b_l only through cos(4b_l - 2p).')
print('  (ii) On the face chart the objective reads (with u = sqrt(Q), e = u/R):')
print('          a_on * phi_on + beta_on e_on^2 + gamma_on e_on')
print('        + a_off * atan2(Y,X) + beta_off e_off^2 + gamma_off e_off')
print('       where the OFF term now has NO cancellation: X^2+Y^2 = Q is a sum of')
print('       three closed-form pieces and u\' = 2r(2 - ... ) etc. are elementary.')
print('  (iii) The quadratic piece is an exact square:')
for jm, (bi, gi) in [(0, (-zJ[16], -zJ[78])), (1, (zJ[20], zJ[82]))]:
    beta = mp.mpf(f'{bi:.9f}'); gam = mp.mpf(f'{gi:.9f}')
    RR = mp.mpf(19)/50
    m = beta/RR**2; nn = gam/RR
    print(f'          j={jm}: beta e^2 + gamma e = m(u - u*)^2 + (gamma^2 - beta^2... )')
    print(f'                m = {mp.nstr(m,10)}, u* = {mp.nstr(nn/(2*m),10) if False else mp.nstr(-nn/(2*m),10)[:14]}')

print()
print('=== exact derivatives of Q in the on-face angle (useful for stationarity) ===')
print('   dQ/dp   = 2 r^2 * (-2 sin(4b_l - 2p)) * (-1) ... differentiate directly:')
r = mp.mpf('0.3795'); b1 = mp.mpf('1.0'); b2 = mp.mpf('0.8')
h = mp.mpf('1e-6')
for pv in ['-0.5', '0.0', '0.4']:
    p = mp.mpf(pv)
    Qp, _ = Q_code(r, b1, b2, p+h, 0)
    Q0, _ = Q_code(r, b1, b2, p, 0)
    Qm, _ = Q_code(r, b1, b2, p-h, 0)
    fd = (Qp-Qm)/(2*h)
    formula = 2*4*r*r*mp.sin(4*b1-2*p)*mp.mpf(0)+8*r*r*mp.sin(4*b1-2*p)
    print(f'   p={pv}: dQ/dp FD = {mp.nstr(fd,12)}   closed 4r^2*2sin(4b1-2p) = '
          f'{mp.nstr(8*r*r*mp.sin(4*b1-2*p),12)}')
