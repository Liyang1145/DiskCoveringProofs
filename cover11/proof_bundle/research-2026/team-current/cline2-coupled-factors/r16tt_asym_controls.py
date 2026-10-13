"""cline2-coupled-factors R16tt: INDEPENDENT Cartesian feasibility countercheck at ASYMMETRIC
b1 != b2, with the constraint surfaces actually ACTIVE.

Construction (no chart identity assumed):
  * choose r, the hub polar radius rho < 1 and hub angle delta;
  * for each of the two sites, |hub - site| = 1 - r on the unit circle pins the site angle
        cos(angle_i - delta) = (1 - (1-r)^2 - rho^2) / (2 rho),
    so  angle_1 = delta + acos(...),  angle_2 = delta - acos(...)   (b1 = delta - angle_1,
        b2 = angle_2 - delta);
  * then the two radius-r disks are TANGENT at the hub, so the hub is on the boundary of
    both caps, while the unit-disk condition is a strict inequality.
  * sweep the hub angle/radius around this configuration to test the filter on both sides
    of feasibility, and compare against the ORIGINAL three Cartesian conditions
        |hub| <= 1 ,  |hub - site_i| >= r .
"""
import math, json
from pathlib import Path
from mpmath import mp

mp.dps = 40
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
R = mp.mpf(19)/50


def cart_status(r, rho, delta, phi1, phi2):
    """the ORIGINAL feasibility: unit disk + two radius-r disks about the sites"""
    hub = mp.matrix([rho*mp.cos(delta), rho*mp.sin(delta)])
    s1 = mp.matrix([mp.cos(phi1), mp.sin(phi1)])
    s2 = mp.matrix([mp.cos(phi2), mp.sin(phi2)])
    d1 = mp.sqrt((hub[0]-s1[0])**2+(hub[1]-s1[1])**2)
    d2 = mp.sqrt((hub[0]-s2[0])**2+(hub[1]-s2[1])**2)
    return dict(inside_unit=bool(rho <= 1), out1=float(d1-r), out2=float(d2-r),
                d1=float(d1), d2=float(d2), hub_ok=bool(rho <= 1),
                feasible=bool(rho <= 1 and d1 >= r and d2 >= r))


def filter_status(r, b1, b2, delta, rho):
    """the chart filter: own cap, opposite cap, norm circle.
    On the face-1 arc H = 2r sin(2b1-delta); we set H = rho*? -- here H is the hub polar
    radius, so the arc condition is H = 2r sin(2b1-delta) with H = rho."""
    H = rho
    cap1 = 2*r*mp.sin(2*b1-delta)
    cap2 = 2*r*mp.sin(2*b2+delta)
    s = mp.sqrt(1-r*r)
    R1 = cap1-H
    R2 = cap2-H
    Nc = -(H*H-2*s*mp.cos(delta)*H+2*r*(1-r))
    return dict(R1=float(R1), R2=float(R2), Nc=float(Nc),
                pred=R1 >= 0 and R2 >= 0 and Nc >= 0)


print('=== ASYMMETRIC CONTROLS: hub on the tangency of BOTH radius-r disks ===')
print()
controls = [(mp.mpf('0.377'), mp.mpf('0.62'), mp.mpf('0.05'), 'b1>b2'),
            (mp.mpf('0.376'), mp.mpf('0.70'), mp.mpf('-0.13'), 'b1<b2'),
            (mp.mpf('0.378'), mp.mpf('0.55'), mp.mpf('0.16'), 'b1>>b2')]
rows = []
for (r, rho, delta, tag) in controls:
    c = (1-(1-r)**2-rho**2)/(2*rho)
    al = mp.acos(c)
    phi1 = delta+al
    phi2 = delta-al
    b1 = delta-phi1          # = -al
    b2 = phi2-delta          # = -al
    # that makes b1 = b2; to force asymmetry we instead pin the two sites at DIFFERENT
    # distances: site 1 tangent (|hub-site1| = 1-r) and site 2 at distance 1-r-sigma.
    sig = mp.mpf('0.05')
    c2 = (1-(1-r-sig)**2-rho**2)/(2*rho)
    if abs(c2) > 1:
        print(f'  {tag}: c2 out of range'); continue
    al1 = mp.acos((1-(1-r)**2-rho**2)/(2*rho))
    al2 = mp.acos(c2)
    phi1 = delta+al1
    phi2 = delta-al2
    b1 = delta-phi1
    b2 = phi2-delta
    cart = cart_status(r, rho, delta, phi1, phi2)
    filt = filter_status(r, b1, b2, delta, rho)
    rows.append((tag, r, rho, delta, b1, b2, cart, filt))
    print(f'  [{tag}] r={float(r)} rho={float(rho)} delta={float(delta)}')
    print(f'     sites at phi1={float(phi1):+.6f}, phi2={float(phi2):+.6f}  '
          f'-> b1 = delta-phi1 = {float(b1):+.6f}, b2 = phi2-delta = {float(b2):+.6f}'
          f'   (asymmetric: b1-b2 = {float(b1-b2):+.6f})')
    print(f'     CARTESIAN: |hub|={float(rho):.6f}<=1 : {cart["hub_ok"]};  '
          f'|hub-c1|-r = {cart["out1"]:+.9f};  |hub-c2|-r = {cart["out2"]:+.9f}  '
          f'-> FEASIBLE = {cart["feasible"]}')
    print(f'     FILTER   : R1={filt["R1"]:+.9f} R2={filt["R2"]:+.9f} Nc={filt["Nc"]:+.9f} '
          f'-> PREDICTS feasible = {filt["pred"]}')
    print(f'     AGREE    : {cart["feasible"] == filt["pred"]}')
    print()

print('=== the corrected R2 identity at these controls ===')
for (tag, r, rho, delta, b1, b2, cart, filt) in rows:
    lhs = 2*r*(mp.sin(2*b2+delta)-mp.sin(2*b1-delta))
    rhs = 4*r*mp.cos(b1+b2)*mp.sin(b2-b1+delta)
    print(f'  [{tag}] 2r[sin(2b2+d)-sin(2b1-d)] = {float(lhs):+.12f}   '
          f'4r cos(b1+b2) sin(b2-b1+d) = {float(rhs):+.12f}   diff = '
          f'{float(abs(lhs-rhs)):.2e}')
    print(f'        and R2 from the filter = {filt["R2"]:+.12f}  (should match lhs)')

print()
print('=== sweep around the control to test both sides of feasibility ===')
for (tag, r, rho, delta, b1, b2, cart, filt) in rows[:2]:
    print(f'  [{tag}] r={float(r)} delta={float(delta)} fixed, hub radius swept:')
    for d_rho in [mp.mpf('-0.05'), mp.mpf('-0.02'), mp.mpf('0'), mp.mpf('0.02'), mp.mpf('0.05')]:
        rho2 = rho+d_rho
        if rho2 <= 0 or rho2 >= 1:
            continue
        al1 = mp.acos((1-(1-r)**2-rho2**2)/(2*rho2))
        c2v = (1-(1-r-mp.mpf('0.05'))**2-rho2**2)/(2*rho2)
        if abs(c2v) > 1:
            print(f'     rho={float(rho2):.4f}: c2 out of range'); continue
        al2 = mp.acos(c2v)
        phi1 = delta+al1; phi2 = delta-al2
        b1n = delta-phi1; b2n = phi2-delta
        cc = cart_status(r, rho2, delta, phi1, phi2)
        ff = filter_status(r, b1n, b2n, delta, rho2)
        print(f'     rho={float(rho2):.4f}: cart feasible={cc["feasible"]} '
              f'(|hub-c1|-r={cc["out1"]:+.6f}, |hub-c2|-r={cc["out2"]:+.6f})   '
              f'filter R1={ff["R1"]:+.6f} R2={ff["R2"]:+.6f} Nc={ff["Nc"]:+.6f} '
              f'pred={ff["pred"]}   AGREE={cc["feasible"]==ff["pred"]}')
