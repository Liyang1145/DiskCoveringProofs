"""cline2-coupled-factors R16uu: asymmetric Cartesian countercheck, correct chart reading.

Correct reading (the one that makes the code's caps coincide with the actual disk
constraints): the hub direction is delta, the site directions are
    phi1 = delta + b1 ,  phi2 = delta - b2 ,
and the hub polar radius on the tangency surface is the smaller root
    h = cos(b) - sqrt(r^2 - sin^2(b)) ,      b = delta - phi  (so b1 = phi1 - delta).
Then  |hub - site| = r  identically, and the cap residual  H - 2r sin(2b - delta)
measures twice the signed difference in distance, so the chart caps ARE the disk filters.

Controls: three ASYMMETRIC configurations (b1 != b2), each with at least one constraint
surface active, plus a sweep that crosses feasibility.  The comparison is against the
ORIGINAL Cartesian conditions  |hub| <= 1  and  |hub - site_i| >= r .
"""
import math, json
from pathlib import Path
from mpmath import mp

mp.dps = 40
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
R = mp.mpf(19)/50


def hub_radius(r, b):
    """smaller root of h^2 - 2 cos(b) h + (1 - r^2) = 0"""
    s2 = r*r-mp.sin(b)**2
    if s2 < 0:
        return None
    return mp.cos(b)-mp.sqrt(s2)


def cart(r, h, delta, phi1, phi2):
    hub = mp.matrix([h*mp.cos(delta), h*mp.sin(delta)])
    s1 = mp.matrix([mp.cos(phi1), mp.sin(phi1)])
    s2 = mp.matrix([mp.cos(phi2), mp.sin(phi2)])
    d1 = mp.sqrt((hub[0]-s1[0])**2+(hub[1]-s1[1])**2)
    d2 = mp.sqrt((hub[0]-s2[0])**2+(hub[1]-s2[1])**2)
    return dict(h=float(h), d1=float(d1), d2=float(d2),
                out1=float(d1-r), out2=float(d2-r),
                feasible=bool(h <= 1 and d1 >= r and d2 >= r))


def filt(r, b1, b2, delta, h):
    cap1 = 2*r*mp.sin(2*b1-delta) if abs(2*b1-delta) <= mp.pi/2 else None
    cap2 = 2*r*mp.sin(2*b2+delta) if abs(2*b2+delta) <= mp.pi/2 else None
    s = mp.sqrt(1-r*r)
    Nc = -(h*h-2*s*mp.cos(delta)*h+2*r*(1-r))
    ok = True
    if cap1 is not None and h > cap1:
        ok = False
    if cap2 is not None and h > cap2:
        ok = False
    if Nc < 0:
        ok = False
    return dict(cap1=None if cap1 is None else float(cap1),
                cap2=None if cap2 is None else float(cap2),
                Nc=float(Nc), pred=ok)


print('=== ASYMMETRIC CONTROLS (b1 != b2), constraints active, checked against the')
print('    ORIGINAL Cartesian disks ===')
print()
controls = [(mp.mpf('0.377'), mp.mpf('0.90'), mp.mpf('0.05'), mp.mpf('1.10'), mp.mpf('0.60')),
            (mp.mpf('0.376'), mp.mpf('0.80'), mp.mpf('-0.10'), mp.mpf('0.55'), mp.mpf('1.20')),
            (mp.mpf('0.378'), mp.mpf('0.70'), mp.mpf('0.00'), mp.mpf('1.25'), mp.mpf('0.45'))]
allagree = True
for (r, h, delta, b1v, b2v) in controls:
    phi1 = delta+b1v
    phi2 = delta-b2v
    # the hub radius forced by tangency to site 1 (using b = b1)
    h1 = hub_radius(r, b1v)
    cc = cart(r, h, delta, phi1, phi2)
    ff = filt(r, b1v, b2v, delta, h)
    agree = (cc['feasible'] == ff['pred'])
    allagree = allagree and agree
    print(f'  r={float(r)} hub h={float(h)} delta={float(delta)}  '
          f'b1={float(b1v)} b2={float(b2v)}  (b1-b2={float(b1v-b2v):+.6f})')
    print(f'     sites: phi1=delta+b1={float(phi1):+.6f}, phi2=delta-b2={float(phi2):+.6f}')
    print(f'     CARTESIAN: |hub-c1|-r = {cc["out1"]:+.9f}, |hub-c2|-r = {cc["out2"]:+.9f},'
          f' |hub|={cc["h"]:.6f}<=1  -> FEASIBLE={cc["feasible"]}')
    print(f'     FILTER   : cap1={ff["cap1"]} cap2={ff["cap2"]} Nc={ff["Nc"]:+.9f} '
          f'-> pred={ff["pred"]}')
    print(f'     AGREE    : {agree}')
    print(f'     (the tangency radius from b1 alone is h1={None if h1 is None else float(h1):.6f})')
    print()

print('=== sweep crossing feasibility (asymmetric, b1 != b2 fixed, h swept) ===')
for (r, h, delta, b1v, b2v) in controls[:2]:
    print(f'  r={float(r)} delta={float(delta)} b1={float(b1v)} b2={float(b2v)}:')
    for dh in [mp.mpf('-0.10'), mp.mpf('-0.05'), mp.mpf('0'), mp.mpf('0.05'), mp.mpf('0.10')]:
        hh = h+dh
        if hh <= 0 or hh >= 1:
            continue
        cc = cart(r, hh, delta, delta+b1v, delta-b2v)
        ff = filt(r, b1v, b2v, delta, hh)
        print(f'     h={float(hh):.4f}: cart={cc["feasible"]} '
              f'(d1-r={cc["out1"]:+.6f}, d2-r={cc["out2"]:+.6f})   '
              f'filter pred={ff["pred"]}  AGREE={cc["feasible"]==ff["pred"]}')

print()
print('=== identity check on these asymmetric controls ===')
for (r, h, delta, b1v, b2v) in controls:
    lhs = 2*r*(mp.sin(2*b2v+delta)-mp.sin(2*b1v-delta))
    rhs = 4*r*mp.cos(b1v+b2v)*mp.sin(b2v-b1v+delta)
    print(f'  b1={float(b1v)} b2={float(b2v)} delta={float(delta)}: lhs={float(lhs):+.12f} '
          f'rhs={float(rhs):+.12f} diff={float(abs(lhs-rhs)):.2e}')
print()
print('ALL CONTROLS AGREE:', allagree)
