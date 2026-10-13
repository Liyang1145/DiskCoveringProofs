"""cline2-coupled-factors R18h: the exact algebraic identities, verified numerically.

From the code:  X = H - 2r sin b cos(ang),  Y = 2r sin b sin(ang),  Q = X^2+Y^2, so
    Q = H^2 + 4r^2 sin^2 b - 4 r H sin b cos(ang)                        (I)
which is the cancellation-free part (no difference of nearly equal terms).

The two free statements to test are:
    T := b1 + b2  enters only through the cross term sin b cos(ang);
    at T = pi/2 the two source DISKS coincide (verified: D1 - D2 = 0).
"""
import json
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']


def code(r, b1, b2, p, j):
    if j == 0:
        A = b1-p; B = b2+p; H = 2*r*mp.sin(2*b1-p); b, ang = b2, B
    else:
        A = b1-p; B = b2+p; H = 2*r*mp.sin(2*b2+p); b, ang = b1, A
    X = H-2*r*mp.sin(b)*mp.cos(ang)
    Y = 2*r*mp.sin(b)*mp.sin(ang)
    return dict(X=X, Y=Y, Q=X*X+Y*Y, H=H, b=b, ang=ang, A=A, B=B)


print('=== identity (I): Q = H^2 + 4r^2 sin^2 b - 4 r H sin b cos(ang) ===')
w1 = 0; n = 0
for j in (0, 1):
    for rv in ['0.379', '0.3793', '0.37999']:
        for ov in ['0.61', '0.8', '1.0', '1.15']:
            for pv in ['-0.9', '-0.4', '0.0', '0.4', '0.9']:
                r = mp.mpf(rv); p = mp.mpf(pv)
                b1 = mp.mpf('1.0') if j == 0 else mp.mpf(ov)
                b2 = mp.mpf(ov) if j == 0 else mp.mpf('1.0')
                D = code(r, b1, b2, p, j)
                rhs = (D['H']**2+4*r*r*mp.sin(D['b'])**2
                       - 4*r*D['H']*mp.sin(D['b'])*mp.cos(D['ang']))
                w1 = max(w1, abs(D['Q']-rhs)); n += 1
print(f'   max deviation over {n} cases = {mp.nstr(w1,4)}')
print()

print('=== how T = b1+b2 enters: examine the cross term ===')
print('   j=0: b = b2, ang = B = b2 + p  ->  sin(b)cos(ang) = sin b2 cos(b2+p)')
print('        b1 enters ONLY through H = 2r sin(2b1-p).')
print('   j=1: b = b1, ang = A = b1 - p  ->  sin(b)cos(ang) = sin b1 cos(b1-p)')
print('        b2 enters ONLY through H = 2r sin(2b2+p).')
print('   => on the face-l chart, the OTHER bearing enters ONLY via H; the on-face')
print('      bearing enters via cos(b_l ∓ p) and via H = 2r sin(2b_l ∓ p).')
print('      T = b1+b2 does NOT appear as a single variable in Q (my earlier claim of a')
print('      cos T collapse was wrong and is withdrawn).')
print()

print('=== the exact stationarity simplification: H-elimination via the circle condition ===')
print('   On face 1 the hub lies on the radius-r circle about c1, so')
print('        H^2 + 1 - 2 H cos(b1 - p) = r^2 .                              (II)')
w2 = 0
for rv in ['0.379', '0.3795', '0.37999']:
    for b1v in ['0.61', '0.8', '1.0', '1.15']:
        for pv in ['-0.8', '-0.2', '0.3', '0.7']:
            r = mp.mpf(rv); b1 = mp.mpf(b1v); p = mp.mpf(pv)
            H = 2*r*mp.sin(2*b1-p)
            lhs = H*H+1-2*H*mp.cos(b1-p)
            w2 = max(w2, abs(lhs-r*r))
print(f'   max |H^2 + 1 - 2H cos(b1-p) - r^2| over the sampled band = {mp.nstr(w2,4)}')
print('   (if this is 0, then H = cos(b1-p) ± sqrt(r^2 - sin^2(b1-p)) is the EXACT closed')
print('    form for H, i.e. the 2r sin(2b1-p) parametrisation is equivalent to the standard')
print('    chord formula; the sign choice selects the arc.)')
print()

print('=== degenerate test T = pi/2: the two source disks coincide ===')
r = mp.mpf('0.3795')
for b1v in ['0.60946080763725372899', '0.8', '1.0', '1.1']:
    b1 = mp.mpf(b1v); b2 = mp.pi/2-b1
    D1 = (r*mp.sin(2*b1), -r*mp.cos(2*b1))
    D2 = (r*mp.sin(2*b2), r*mp.cos(2*b2))
    print(f'   b1={b1v:22s} b2={mp.nstr(b2,10)}: |D1-D2| = {mp.nstr(mp.sqrt((D1[0]-D2[0])**2+(D1[1]-D2[1])**2),4)}')
print('   => at T = pi/2 the two radius-r disks are the SAME disk, so the corner picture')
print('      degenerates and the entire common arc must be retained (confirmed).')
print()

print('=== the exact square for the radial quadratic (the second useful identity) ===')
for jm, (bi, gi) in [(0, (-zJ[16], -zJ[78])), (1, (zJ[20], zJ[82]))]:
    beta = mp.mpf(f'{bi:.9f}'); gam = mp.mpf(f'{gi:.9f}'); RR = mp.mpf(19)/50
    m = beta/RR**2; nn = gam/RR
    print(f'   j={jm}: beta e^2 + gamma e = m(u - u*)^2 - n^2/(4m) with')
    print(f'          m = {mp.nstr(m,12)},  u* = -n/(2m) = {mp.nstr(-nn/(2*m),12)},  '
          f'remainder = {mp.nstr(-nn*nn/(4*m),12)}')
    # verify at a few u
    wr = 0
    for uv in ['0.05', '0.2', '0.40784', '0.6', '0.75']:
        u = mp.mpf(uv)
        lhs = beta*(u/RR)**2+gam*(u/RR)
        rhs = m*(u+nn/(2*m))**2-nn*nn/(4*m)
        wr = max(wr, abs(lhs-rhs))
    print(f'          max deviation over u samples = {mp.nstr(wr,4)}')
