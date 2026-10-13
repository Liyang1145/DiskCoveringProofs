"""cline2-coupled-factors R16zz: Cartesian controls built EXACTLY from the lead's disk
construction (no invented geometry).

Read from lead/interval_hub_boundary.py:11:
    disks = [ ( r sin2b1, -r cos2b1,  r ),
              ( r sin2b2,  r cos2b2,  r ),
              ( s,          0,       1-r ) ]            s = sqrt(1-r^2)
so the radius-r disks are centred at
    D1 = (r sin 2b1, -r cos 2b1),   D2 = (r sin 2b2, +r cos 2b2),
and the unit-disk condition is the disk of radius 1-r about (s, 0).

With the hub x = (H cos delta, H sin delta) the exact residual identities are
    |x - D1|^2 - r^2 = H (H - 2r sin(2b1-delta)) = -H R1
    |x - D2|^2 - r^2 = H (H - 2r sin(2b2+delta)) = -H R2
    |x - (s,0)|^2 - (1-r)^2 = H^2 - 2 s H cos delta + 2r(1-r) = -N
so a POSITIVE disk-distance residual means the hub is INSIDE that disk, i.e. ILLEGAL.

Controls required before any further work:
    A) two LEGAL off-ridge configurations,
    B) one ILLEGAL off-ridge configuration whose positive disk residual is confirmed,
each with D1, D2 FIXED (built from (r,b1,b2)) while H is perturbed.
"""
import math, json
from pathlib import Path
from mpmath import mp

mp.dps = 40
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'

print('=== identities, verified symbolically/numerically at 40 dps ===')


def build(r, b1, b2):
    s = mp.sqrt(1-r*r)
    D1 = (r*mp.sin(2*b1), -r*mp.cos(2*b1))
    D2 = (r*mp.sin(2*b2), r*mp.cos(2*b2))
    C = (s, mp.mpf(0))
    return D1, D2, C, s


def cart_residuals(r, b1, b2, H, delta):
    """the ORIGINAL three Cartesian quantities"""
    D1, D2, C, s = build(r, b1, b2)
    x = (H*mp.cos(delta), H*mp.sin(delta))
    out = []
    for D in (D1, D2):
        out.append((x[0]-D[0])**2+(x[1]-D[1])**2-r*r)
    out.append((x[0]-C[0])**2+x[1]**2-(1-r)**2)
    return out


def chart_residuals(r, b1, b2, H, delta):
    s = mp.sqrt(1-r*r)
    R1 = 2*r*mp.sin(2*b1-delta)-H
    R2 = 2*r*mp.sin(2*b2+delta)-H
    N = 2*s*mp.cos(delta)*H-H*H-2*r*(1-r)
    return [(-H*R1), (-H*R2), (-N)]


print(f'{"r":>7s} {"b1":>7s} {"b2":>7s} {"H":>9s} {"delta":>8s} | '
      f'{"cart1":>12s} {"chart1":>12s} {"cart2":>12s} {"chart2":>12s} '
      f'{"cartN":>12s} {"chartN":>12s}')
maxdiff = 0
import random
random.seed(11)
for _ in range(6):
    r = mp.mpf(str(random.uniform(.375, .38)))
    b1 = mp.mpf(str(random.uniform(1.0, 1.18)))
    b2 = mp.mpf(str(random.uniform(1.0, 1.18)))
    H = mp.mpf(str(random.uniform(.1, .9)))
    d = mp.mpf(str(random.uniform(-1.0, 1.0)))
    ca = cart_residuals(r, b1, b2, H, d)
    ch = chart_residuals(r, b1, b2, H, d)
    for a, b in zip(ca, ch):
        maxdiff = max(maxdiff, abs(a-b))
    print(f'{float(r):7.5f} {float(b1):7.5f} {float(b2):7.5f} {float(H):9.6f} '
          f'{float(d):8.5f} | {float(ca[0]):12.3e} {float(ch[0]):12.3e} '
          f'{float(ca[1]):12.3e} {float(ch[1]):12.3e} {float(ca[2]):12.3e} '
          f'{float(ch[2]):12.3e}')
print(f'\n  max |cartesian - chart| over the identities: {mp.nstr(maxdiff,6)}')

print()
print('=== CONTROLS: D1, D2 built from (r,b1,b2) and FIXED; H perturbed ===')
print('   legal  <=> both disk residuals <= 0 and the norm residual <= 0')
print()
controls = []
# two LEGAL off-ridge and one ILLEGAL off-ridge
specs = [
    ('A-legal-1', mp.mpf('0.377'), mp.mpf('1.10'), mp.mpf('1.05'), mp.mpf('-0.32')),
    ('A-legal-2', mp.mpf('0.378'), mp.mpf('1.06'), mp.mpf('1.12'), mp.mpf('0.38')),
    ('B-illegal-1', mp.mpf('0.377'), mp.mpf('1.10'), mp.mpf('1.05'), mp.mpf('0.60')),
]
for (tag, r, b1, b2, delta) in specs:
    D1, D2, C, s = build(r, b1, b2)
    cap1 = 2*r*mp.sin(2*b1-delta)
    cap2 = 2*r*mp.sin(2*b2+delta)
    print(f'  [{tag}] r={float(r)} b1={float(b1)} b2={float(b2)} delta={float(delta)}')
    print(f'     D1=({float(D1[0]):+.6f},{float(D1[1]):+.6f})  '
          f'D2=({float(D2[0]):+.6f},{float(D2[1]):+.6f})  C=({float(C[0]):+.6f},0)  '
          f'|D1|={float(mp.sqrt(D1[0]**2+D1[1]**2)):.6f} (should be r)')
    print(f'     cap1 = 2r sin(2b1-delta) = {float(cap1):.6f} ; '
          f'cap2 = 2r sin(2b2+delta) = {float(cap2):.6f}')
    for H, htag in [(cap1, 'H=cap1'), ((cap1+cap2)/2, 'H=mid'),
                    (min(cap1, cap2)-mp.mpf('0.05'), 'H=min-0.05')]:
        if H <= 0 or H >= 2*r:
            H = m if False else H
        if H <= 0:
            continue
        ca = cart_residuals(r, b1, b2, H, delta)
        legal = all(v <= 0 for v in ca)
        controls.append((tag, htag, r, b1, b2, delta, H, ca, legal))
        print(f'       {htag:12s} H={float(H):.6f}: '
              f'disk1={float(ca[0]):+.6e} disk2={float(ca[1]):+.6e} '
              f'norm={float(ca[2]):+.6e}  -> {"LEGAL" if legal else "ILLEGAL"}')
    print()

print('=== the required three controls, restated ===')
need = []
for (tag, htag, r, b1, b2, delta, H, ca, legal) in controls:
    if legal and 'legal' in tag:
        need.append((tag, htag, legal))
    if (not legal) and 'illegal' in tag:
        need.append((tag, htag, legal))
legal_cnt = sum(1 for (tag, ht, lg) in need if lg)
ill_cnt = sum(1 for (tag, ht, lg) in need if not lg)
print(f'  legal controls found : {legal_cnt} (need >= 2 off-ridge)')
print(f'  illegal controls found: {ill_cnt} (need >= 1 off-ridge, positive disk residual)')
for (tag, ht, lg) in need:
    print(f'     {tag:12s} {ht:12s} legal={lg}')

print()
print('=== off-ridge check ===')
for (tag, htag, r, b1, b2, delta, H, ca, legal) in controls:
    A = b1-delta; B = b2+delta
    off = abs(b1-b2) > 1e-9
    print(f'  {tag:12s} {htag:12s}: delta={float(delta):+.4f}, b1-b2={float(b1-b2):+.4f} '
          f'-> off-ridge={off}, legal={legal}')
json.dump([[str(x) for x in (tag, htag, r, b1, b2, delta, H, legal)]
           for (tag, htag, r, b1, b2, delta, H, ca, legal) in controls],
          open(OUT/'r16zz_controls.json', 'w'), indent=1)
print('\nsaved out/r16zz_controls.json')
