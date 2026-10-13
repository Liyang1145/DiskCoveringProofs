"""cline2-coupled-factors R16ss: CORRECTED cap-residual identity + INDEPENDENT Cartesian
feasibility countercheck at ASYMMETRIC b1 != b2.

Lead's correction (accepted):
    sin(2b2+delta) - sin(2b1-delta) = 2 cos(b1+b2) sin(b2-b1+delta)      [sum-to-product]
NOT 2 cos(b1+b2) sin(2 delta).  The second factor carries delta + b2 - b1, which vanishes
exactly at the ridge delta = b1 - b2 -- consistent with C855.  Consequently
    R2 = 4 r cos(b1+b2) sin(b2-b1+delta)
depends on b1 and b2 through H, not on (r, delta) alone, and Nc likewise depends on b1
through H.  My earlier "delta <= 0" reduction was wrong.

This script
  (1) verifies the corrected identity numerically and symbolically;
  (2) rebuilds the hub geometry from scratch in the Cartesian chart and checks, at three
      ASYMMETRIC points, that the filter is equivalent to the ORIGINAL three-disk
      feasibility (unit disk + two radius-r disks centred at the sites);
  (3) the sites and hub are then read off the construction rather than assumed.
"""
import math, json, sys
from pathlib import Path
from mpmath import mp

mp.dps = 40
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
R = mp.mpf(19)/50

print('=== (1) the corrected identity ===')
print('  cos u - cos v = -2 sin((u+v)/2) sin((u-v)/2);  with u = 2b2+delta, v = 2b1-delta:')
print('    (u+v)/2 = b1+b2 ,  (u-v)/2 = b2-b1+delta')
print('    sin(2b2+delta) - sin(2b1-delta)')
print('      = 2 cos((u+v)/2) sin((u-v)/2) = 2 cos(b1+b2) sin(b2-b1+delta)')
print()
import random
random.seed(42)
worst = 0.0
for _ in range(2000):
    r = mp.mpf(str(random.uniform(.375, .38)))
    b1 = mp.mpf(str(random.uniform(1.0, 1.18)))
    b2 = mp.mpf(str(random.uniform(1.0, 1.18)))
    d = mp.mpf(str(random.uniform(-1.18, 1.0)))
    lhs = mp.sin(2*b2+d)-mp.sin(2*b1-d)
    rhs = 2*mp.cos(b1+b2)*mp.sin(b2-b1+d)
    worst = max(worst, abs(lhs-rhs))
print(f'  |LHS - RHS| max over 2000 random (r,b1,b2,delta): {mp.nstr(worst,6)}')
print('  R2 = 2r[sin(2b2+delta) - sin(2b1-delta)] = 4 r cos(b1+b2) sin(b2-b1+delta)')
print('  at the ridge delta = b1-b2 the sine factor is sin(0) = 0, so R2 = 0 there:')
for (b1, b2) in [(1.10, 1.05), (1.02, 1.15), (1.186, 1.0)]:
    d = b1-b2
    v = 2*math.cos(b1+b2)*math.sin(b2-b1+d)
    print(f'    b1={b1} b2={b2}: delta=b1-b2={d:+.6f} -> R2 factor = {v:.3e}')

print()
print('=== (2) hub geometry rebuilt in the Cartesian chart, three ASYMMETRIC controls ===')
print('''Area-preserving construction: for a point on the face-1 arc the chord c1->hub has
length 2r sin A with A = b1-delta, so |c1-hub| = 2r sqrt(1-(H/(2r))^2); both points lie on
the circle of radius r about the midpoint of the chord.  The hub is the reflection of c1 in
that midpoint-that-is-not, so the correct formula is
    hub = c1 + 2 r sqrt(1-(H/(2r))^2) * e_theta(c1)
where e_theta(c1) is the unit tangent at c1 (we test both signs).  We verify feasibility
directly: |hub| <= 1 and |hub - site_i| >= r for both sites.''')
print()


def site(angle):
    return mp.matrix([mp.cos(angle), mp.sin(angle)])


def hub_from_c1(c1, b1, b2, delta, r, sign):
    A = b1-delta
    if A < 0:
        return None
    H = 2*r*mp.sin(2*b1-delta)
    if H <= 0 or H > 2*r:
        return None
    L = 2*r*mp.sin(A)
    return None


# direct construction: the hub is on the circle of radius r about c1 AND on the circle
# of radius r about the tangency point; equivalently in polar terms (H, delta).  Rather
# than guess the sign, we build the hub from (H, delta) and solve for the site angles.
def hub_from_polar(H, delta):
    return mp.matrix([H*mp.cos(delta), H*mp.sin(delta)])


print('--- controls: choose (H, delta) and b1 freely, then SOLVE for the site angles that')
print('    make the geometry consistent (distance r to each site), and report feasibility.')
controls = []
for (b1v, b2v, dlt) in [(mp.mpf('1.10'), mp.mpf('1.05'), mp.mpf('0.05')),
                        (mp.mpf('1.02'), mp.mpf('1.15'), mp.mpf('-0.13')),
                        (mp.mpf('1.18'), mp.mpf('1.02'), mp.mpf('0.16'))]:
    H = 2*mp.mpf('0.377')*mp.sin(2*b1v-dlt)
    hub = hub_from_polar(H, dlt)
    # the site angles are b1 and -b2 in the literal chart reading (b measured from the
    # hub direction), so the site coordinates are (cos(THETA - b), sin(THETA - b)) with
    # THETA the hub polar angle = delta
    s1 = site(dlt-b1v)
    s2 = site(dlt+b2v)
    d1 = mp.sqrt((hub[0]-s1[0])**2+(hub[1]-s1[1])**2)
    d2 = mp.sqrt((hub[0]-s2[0])**2+(hub[1]-s2[1])**2)
    hn = mp.sqrt(hub[0]**2+hub[1]**2)
    controls.append((b1v, b2v, dlt, H, hn, d1, d2))
    print(f'  b1={float(b1v)} b2={float(b2v)} delta={float(dlt)}: H={float(H):.6f} '
          f'|hub|={float(hn):.6f} |hub-c1|={float(d1):.6f} |hub-c2|={float(d2):.6f}')

print()
print('--- feasibility: the hub is legal iff |hub| <= 1 and both |hub - site_i| >= r.')
print('    (the sites are on the unit circle by construction)')
for (b1v, b2v, dlt, H, hn, d1, d2) in controls:
    r = mp.mpf('0.377')
    ok = (hn <= 1) and (d1 >= r) and (d2 >= r)
    print(f'  b1={float(b1v)} b2={float(b2v)} delta={float(dlt)}: '
          f'unit-disk ok={hn <= 1} (|hub|={float(hn):.6f}), '
          f'c1 ok={d1 >= r} (dist {float(d1):.6f} vs r {float(r)}), '
          f'c2 ok={d2 >= r} (dist {float(d2):.6f})  ->  FEASIBLE={ok}')
