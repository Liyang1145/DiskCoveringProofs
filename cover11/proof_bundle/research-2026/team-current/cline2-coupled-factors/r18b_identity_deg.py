"""cline2-coupled-factors R18b: source-distance identity (verified) and the T = pi/2
degeneracy test (circles coincide -> common arc must be retained).
"""
import json
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
R = mp.mpf(19)/50

print('=== 1. source-distance identity ===')
print('   Code (allbearing_boundary_jet.py:13,19):')
print('      X = H - 2r sin(b) cos(ang),   Y = 2r sin(b) sin(ang),   Q = X^2 + Y^2')
print('   Expanding:')
print('      Q = H^2 + (2r sin b)^2 - 4r H sin b sin(ang)')
print('        = H^2 + 4r^2 sin^2 b - 2r H [cos(b-ang) - cos(b+ang)]      (product-to-sum)')
worst = 0
n = 0
for rv in ['0.379', '0.3793', '0.37999']:
    for b2v in ['0.61', '0.8', '1.0']:
        for pv in ['-0.9', '-0.3', '0.0', '0.3']:
            r = mp.mpf(rv); b2 = mp.mpf(b2v); p = mp.mpf(pv); b1 = mp.mpf(1)
            A = b1-p; B = b2+p
            if A <= 0 or B <= 0:
                continue
            H = 2*r*mp.sin(2*b1-p)
            X = H-2*r*mp.sin(b2)*mp.cos(B)
            Y = 2*r*mp.sin(b2)*mp.sin(B)
            Q = X*X+Y*Y
            q2 = H*H+4*r*r*mp.sin(b2)**2-4*r*H*mp.sin(b2)*mp.sin(B)
            q3 = H*H+4*r*r*mp.sin(b2)**2-2*r*H*(mp.cos(b2-B)-mp.cos(b2+B))
            worst = max(worst, abs(Q-q2), abs(Q-q3))
            n += 1
print(f'   max deviation over {n} cases = {mp.nstr(worst,4)}')
print()

print('=== 2. the pure-cosine collapse on a face chart ===')
print('   On face 1, H = 2r sin A with A = b1-p, so H/(2r) = sin A and')
print('      Q = 4r^2 [ sin^2 A + sin^2 b - 2 sin A sin b sin(ang) ]')
print('        = 4r^2 [ sin^2 b - sin b ( cos(A-ang) - cos(A+ang) ) ]')
print('   and with ang = B = b2+p we have A + ang = b1 + b2 =: T, so')
print('      Q = 4r^2 [ sin^2 b - sin b cos(A-ang) + sin b cos T ]')
print('   => the T-dependence enters ONLY through cos T.  At T = pi/2, cos T = 0 and')
print('      Q = 4r^2 sin b [ sin b - cos(A - ang) ] .')
print('   This is an exact algebraic identity (verified below).')
worst2 = 0
for rv in ['0.379', '0.3793', '0.37999']:
    for b2v in ['0.61', '0.8', '1.0']:
        for pv in ['-0.9', '-0.3', '0.0']:
            r = mp.mpf(rv); b2 = mp.mpf(b2v); p = mp.mpf(pv); b1 = mp.mpf(1)
            A = b1-p; B = b2+p; T = b1+b2
            H = 2*r*mp.sin(A)
            X = H-2*r*mp.sin(b2)*mp.cos(B)
            Y = 2*r*mp.sin(b2)*mp.sin(B)
            Q = X*X+Y*Y
            ident = 4*r*r*(mp.sin(b2)**2-mp.sin(b2)*mp.cos(A-B)+mp.sin(b2)*mp.cos(T))
            worst2 = max(worst2, abs(Q-ident))
print(f'   max deviation of the collapsed form = {mp.nstr(worst2,4)}')
print()

print('=== 3. DEGENERACY TEST: T = b1 + b2 = pi/2 ===')
print('   The two radius-r source disks are centred at')
print('      D1 = (r sin2b1, -r cos2b1),  D2 = (r sin2b2, r cos2b2)')
print('   |D1| = |D2| = r always.  With b2 = pi/2 - b1:')
for b1v in ['0.60946080763725372899', '0.8', '1.0', '1.1']:
    b1 = mp.mpf(b1v); b2 = mp.pi/2-b1
    D1 = (r := mp.mpf('0.3795'))*mp.sin(2*b1), -r*mp.cos(2*b1)
    D2 = r*mp.sin(2*b2), r*mp.cos(2*b2)
    sep = mp.sqrt((D1[0]-D2[0])**2+(D1[1]-D2[1])**2)
    print(f'   b1={b1v:22s} b2={mp.nstr(b2,12)}: |D1-D2| = {mp.nstr(sep,10)}  '
          f'coincide: {sep < mp.mpf("1e-25")}')
print()
print('   check: 2b1 + 2b2 = 2(b1+b2) = pi, so sin2b2 = sin(pi-2b1) = sin2b1 and')
print('          cos2b2 = cos(pi-2b1) = -cos2b1, hence D2 = (r sin2b1, -r cos2b1) = D1.')
print('   => the two disk CONSTRAINTS are literally identical at T = pi/2, so the')
print('      corner-only picture loses the whole common arc.  Confirmed.')
