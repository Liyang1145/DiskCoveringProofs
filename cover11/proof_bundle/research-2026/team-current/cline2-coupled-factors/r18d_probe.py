"""cline2-coupled-factors R18d: find the CORRECT T-dependence of the source squared distance.

Numerical probe: for each (r, b2, p) compute Q and compare against candidate expressions,
to see exactly how T = b1+b2 enters.
"""
import json
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']


def Q_of(r, b1, b2, p, j):
    if j == 0:
        A = b1-p; B = b2+p; H = 2*r*mp.sin(2*b1-p)
        b, ang = b2, B
    else:
        A = b1-p; B = b2+p; H = 2*r*mp.sin(2*b2+p)
        b, ang = b1, A
    X = H-2*r*mp.sin(b)*mp.cos(ang)
    Y = 2*r*mp.sin(b)*mp.sin(ang)
    return X*X+Y*Y, H, b, ang


print('=== does T = b1+b2 determine Q given (r, b1, p) and the OTHER b? ===')
print('   Test: fix r, b2, p; vary b1; watch Q and T = b1+b2.')
r = mp.mpf('0.379'); b2 = mp.mpf('0.8'); p = mp.mpf('0.0')
for b1v in ['0.61', '0.8', '1.0', '1.2']:
    b1 = mp.mpf(b1v)
    Q, H, b, ang = Q_of(r, b1, b2, p, 0)
    T = b1+b2
    print(f'   b1={b1v:5s} T={mp.nstr(T,8)}  H={mp.nstr(H,10)}  Q={mp.nstr(Q,12)}')
print()
print('=== candidate: Q = H^2 + 4r^2 sin^2 b - 4 r H sin b sin(ang), and on a face chart')
print('    H = 2r sin(b1+A), so H^2 contributes a cos^2(b1) sin^2 A part that is NOT')
print('    absorbed by the algebra.  Instead test the FULL algebraic collapse:')
print()
print('   Q = 4r^2 [ sin^2 b + sin^2(b1+A) - 2 sin b sin(b1+A) sin(ang) ]')
worst = 0
for rv in ['0.379', '0.3793', '0.37999']:
    for b2v in ['0.61', '0.8', '1.0']:
        for pv in ['-0.9', '-0.3', '0.0', '0.3']:
            r = mp.mpf(rv); b2 = mp.mpf(b2v); p = mp.mpf(pv); b1 = mp.mpf(1)
            A = b1-p; B = b2+p
            H = 2*r*mp.sin(2*b1-p)
            b, ang = b2, B
            Q, _, _, _ = Q_of(r, b1, b2, p, 0)
            cand = 4*r*r*(mp.sin(b)**2+mp.sin(b1+A)**2
                          - 2*mp.sin(b)*mp.sin(b1+A)*mp.sin(ang))
            worst = max(worst, abs(Q-cand))
print(f'   max deviation = {mp.nstr(worst,4)}')
print()
print('=== the T-structure: write 2b1-p = b1+A and ang = B; then')
print('    sin(2b1-p) sin(B) with A+ang = T:')
print('    sin(b1+A) sin(ang) = [cos(b1+A-ang) - cos(b1+A+ang)]/2')
print('                       = [cos(2b1-2p-... )] -- expand with the actual cases')
worst2 = 0
for rv in ['0.379', '0.3793', '0.37999']:
    for b2v in ['0.61', '0.8', '1.0']:
        for pv in ['-0.9', '-0.3', '0.0', '0.3']:
            r = mp.mpf(rv); b2 = mp.mpf(b2v); p = mp.mpf(pv); b1 = mp.mpf(1)
            A = b1-p; B = b2+p; T = b1+b2
            Q, _, _, _ = Q_of(r, b1, b2, p, 0)
            # exact expansion using X = 2b1-p, and the second factor sin(B)
            cand = 4*r*r*(mp.sin(b2)**2+mp.sin(2*b1-p)**2
                          - 2*mp.sin(b2)*mp.sin(2*b1-p)*mp.sin(B))
            worst2 = max(worst2, abs(Q-cand))
print(f'   Q = 4r^2[sin^2 b + sin^2(2b1-p) - 2 sin b sin(2b1-p) sin B]: '
      f'max dev = {mp.nstr(worst2,4)}')
print()
print('=== so the quantities that matter are X := 2b1-p and B := b2+p, and:')
print('    X + B = 2b1+b2 = (b1+b2) + b1 = T + b1')
print('    X - B = 2b1-b2-2p')
print('   meaning the cross term splits into cos(b2-X) and cos(b2+X) with')
print('    b2+X = b2+2b1-p and b2-X = b2-2b1+p.')
print('   => NO single T-collapse; the correct statement is the one below.')
