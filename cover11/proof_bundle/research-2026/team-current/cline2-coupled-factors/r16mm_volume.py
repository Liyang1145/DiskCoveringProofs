"""cline2-coupled-factors R16mm: does the legal set have interior volume, and where?
Quick numerical probe (not a proof)."""
import math, json, sys
from pathlib import Path
from mpmath import mp

mp.dps = 25
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
R = mp.mpf(19)/50
C0 = mp.mpf(f'{zJ[3]-zJ[1]:.9f}')
XX1 = mp.mpf(f'{zJ[1]-zJ[9]:.9f}'); XX2 = mp.mpf(f'{zJ[3]-zJ[9]:.9f}')
BE1 = mp.mpf(f'{-zJ[16]:.9f}'); GA1 = mp.mpf(f'{-zJ[78]:.9f}')
BE2 = mp.mpf(f'{zJ[20]:.9f}');  GA2 = mp.mpf(f'{zJ[82]:.9f}')


def residuals(r, b1, b2, dl, face):
    s = mp.sqrt(1-r*r)
    A = b1-dl; B = b2+dl
    c1 = 2*r*mp.sin(2*b1-dl); c2 = 2*r*mp.sin(2*b2+dl)
    H = c1 if face == 1 else c2
    R1 = c1-H; R2 = c2-H
    Nc = -(H*H-2*s*mp.cos(dl)*H+2*r*(1-r))
    return R1, R2, Nc, H


print('=== margin of the tightest residual over a numerical grid (bounded probe) ===')
best = {}
nlegal = 0
N = 25
for face in (1, 2):
    bhi = math.acos(0.375)
    worst = None
    for i in range(N):
        r = mp.mpf(str(0.375+(0.38-0.375)*i/(N-1)))
        for a in range(N):
            b1 = mp.mpf(str(1.0+(bhi-1.0)*a/(N-1)))
            for c in range(N):
                b2 = mp.mpf(str(1.0+(bhi-1.0)*c/(N-1)))
                for m in range(41):
                    d = mp.mpf(str(-bhi))+(2*mp.mpf(str(bhi)))*m/40
                    R1, R2, Nc, H = residuals(r, b1, b2, d, face)
                    if H > 0 and R1 >= 0 and R2 >= 0 and Nc >= 0:
                        nlegal += 1
                        mn = min(R1, R2, Nc)
                        if worst is None or mn < worst[0]:
                            worst = (float(mn), float(r), float(b1), float(b2), float(d))
    best[face] = worst
    if worst:
        print(f'  face {face}: legal samples {nlegal}; smallest positive residual '
              f'{worst[0]:.3e} at r={worst[1]:.6f} b1={worst[2]:.6f} b2={worst[3]:.6f} '
              f'd={worst[4]:.6f}')
    else:
        print(f'  face {face}: no legal samples found in the grid!')
print(f'total legal samples: {nlegal}')

print()
print('=== which residual binds at the legal boundary? ===')
for face in (1, 2):
    cnt = dict(R1=0, R2=0, Nc=0)
    for i in range(9):
        r = mp.mpf(str(0.375+(0.38-0.375)*i/8))
        bhi = math.acos(float(r))
        for a in range(7):
            b1 = mp.mpf(str(1.0+(bhi-1.0)*a/6))
            for c in range(7):
                b2 = mp.mpf(str(1.0+(bhi-1.0)*c/6))
                for m in range(101):
                    d = mp.mpf(str(-bhi))+(2*mp.mpf(str(bhi)))*m/100
                    R1, R2, Nc, H = residuals(r, b1, b2, d, face)
                    if H <= 0:
                        continue
                    mn = min(R1, R2, Nc)
                    if abs(mn) < 1e-6:
                        for nm, v in (('R1', R1), ('R2', R2), ('Nc', Nc)):
                            if abs(v-mn) < 1e-9:
                                cnt[nm] += 1
    print(f'  face {face}: active-residual counts on the sampled boundary: {cnt}')
