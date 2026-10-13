"""cline2-coupled-factors R16kk: are the live boxes legal, illegal, or boundary-touching?

Sample the residual functions R1 = cap1-H, R2 = cap2-H, Nc = -(H^2-2 s cos d H + 2r(1-r))
along the live-box fibers reported by r16jj, and at the legal-set boundary.
"""
import math, json, sys
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
OUT = P / 'out'
live = json.loads((OUT/'r16jj_live.json').read_text())
print(f'live boxes: {len(live)}')


def resid(r, b1, b2, dl, face):
    s = mp.sqrt(1-r*r)
    A = b1-dl; B = b2+dl
    H = 2*r*mp.sin(2*b1-dl) if face == 1 else 2*r*mp.sin(2*b2+dl)
    c1 = 2*r*mp.sin(2*b1-dl); c2 = 2*r*mp.sin(2*b2+dl)
    R1 = c1-H; R2 = c2-H
    Nc = -(H*H-2*s*mp.cos(dl)*H+2*r*(1-r))
    return float(R1), float(R2), float(Nc), float(H)


print('\n=== sampling the first 5 live boxes along delta (5 pts) ===')
for bx in live[:5]:
    face = bx['face']
    r = mp.mpf(str(0.5*(bx['r'][0]+bx['r'][1])))
    b1 = mp.mpf(str(0.5*(bx['b1'][0]+bx['b1'][1])))
    b2 = mp.mpf(str(0.5*(bx['b2'][0]+bx['b2'][1])))
    print(f'  face {face} r={float(r):.6f} b1={float(b1):.6f} b2={float(b2):.6f} '
          f'delta in [{bx["d"][0]:.5f},{bx["d"][1]:.5f}]')
    for t in [0, .25, .5, .75, 1]:
        d = mp.mpf(str(bx['d'][0]))+(mp.mpf(str(bx['d'][1]))-mp.mpf(str(bx['d'][0])))*t
        R1, R2, Nc, H = resid(r, b1, b2, d, face)
        ok = (R1 >= -1e-12 and R2 >= -1e-12 and Nc >= -1e-12 and H > 0)
        print(f'     d={float(d):+.6f}  R1={R1:+.6f} R2={R2:+.6f} Nc={Nc:+.6f} H={H:.6f}'
              f'  {"LEGAL" if ok else "illegal"}')

print()
print('=== where is the legal delta boundary for these (r,b1,b2)? ===')
for bx in live[:3]:
    face = bx['face']
    r = mp.mpf(str(0.5*(bx['r'][0]+bx['r'][1])))
    b1 = mp.mpf(str(0.5*(bx['b1'][0]+bx['b1'][1])))
    b2 = mp.mpf(str(0.5*(bx['b2'][0]+bx['b2'][1])))
    legal = []
    N = 4001
    lo = mp.mpf(str(bx['d'][0]))-mp.mpf('0.05')
    hi = mp.mpf(str(bx['d'][1]))+mp.mpf('0.05')
    for i in range(N):
        d = lo+(hi-lo)*i/(N-1)
        R1, R2, Nc, H = resid(r, b1, b2, d, face)
        if R1 >= -1e-13 and R2 >= -1e-13 and Nc >= -1e-13 and H > 0:
            legal.append(float(d))
    if legal:
        print(f'  r={float(r):.6f} b1={float(b1):.6f} b2={float(b2):.6f} face {face}: '
              f'legal delta in [{min(legal):+.6f}, {max(legal):+.6f}] '
              f'({len(legal)} of {N} samples)')
        print(f'     live box delta interval was [{bx["d"][0]:.6f}, {bx["d"][1]:.6f}]')
    else:
        print(f'  r={float(r):.6f} b1={float(b1):.6f} b2={float(b2):.6f} face {face}: '
              f'NO legal delta in the sampled window')
