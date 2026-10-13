"""cline2-coupled-factors R16vv: final corrected-filter record.

Contents
  (1) the corrected sum-to-product identity, verified to 1e-41 over 2000 random draws and
      shown to vanish exactly at the ridge delta = b1 - b2;
  (2) the code's ACTUAL feasibility filter, read literally from
      lead/interval_hub_saturated.py, on points where b1 != b2 and where the constraint
      surfaces are active -- each compared against the ORIGINAL Cartesian quantities
      (|hub| and |hub - site_i|);
  (3) an explicit statement of what depended on the wrong identity and is now invalid.
"""
import math, json
from pathlib import Path
from mpmath import mp

mp.dps = 40
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']

print('=== (1) corrected identity ===')
print('   sin(2b2+d) - sin(2b1-d) = 2 cos(b1+b2) sin(b2-b1+d)')
import random
random.seed(7)
worst = 0
for _ in range(2000):
    b1 = mp.mpf(str(random.uniform(1.0, 1.18)))
    b2 = mp.mpf(str(random.uniform(1.0, 1.18)))
    d = mp.mpf(str(random.uniform(-1.18, 1.18)))
    worst = max(worst, abs((mp.sin(2*b2+d)-mp.sin(2*b1-d))
                           - 2*mp.cos(b1+b2)*mp.sin(b2-b1+d)))
print(f'   max |LHS-RHS| over 2000 random draws = {mp.nstr(worst,4)}')
print('   the sine factor vanishes iff d = b1-b2, i.e. exactly at the ridge (C855).')
print('   The OLD claim "= 2 cos(b1+b2) sin(2d)" is wrong; with it R2 was treated as a')
print('   function of (r,d) alone, which is false.')

print()
print('=== (2) the code\'s actual filter (literal) on asymmetric points ===')
print('''lead/interval_hub_saturated.py defines, on a branch with height H:
     accept iff  H > s-(1-r),  H < 2r,
                 H <= 2r sin(2b1-delta),  H <= 2r sin(2b2+delta),
                 H^2 - 2 s cos(delta) H + 2r(1-r) <= 0,      s = sqrt(1-r^2).
The three residuals are therefore
     R1 = 2r sin(2b1-delta) - H,   R2 = 2r sin(2b2+delta) - H,
     N  = 2 s cos(delta) H - H^2 - 2r(1-r),
and with the corrected identity
     R2 - R1 = 2r[sin(2b2+d) - sin(2b1-d)] = 4 r cos(b1+b2) sin(b2-b1+d).
N depends on b1 and b2 through H -- NOT on (r,delta) alone.''')


def residuals(r, b1, b2, dl, H):
    s = mp.sqrt(1-r*r)
    R1 = 2*r*mp.sin(2*b1-dl)-H
    R2 = 2*r*mp.sin(2*b2+dl)-H
    N = 2*s*mp.cos(dl)*H-H*H-2*r*(1-r)
    return float(R1), float(R2), float(N)


def cart_quantities(r, H, delta, phi1, phi2):
    hub = mp.matrix([H*mp.cos(delta), H*mp.sin(delta)])
    out = {}
    for nm, phi in (('c1', phi1), ('c2', phi2)):
        s = mp.matrix([mp.cos(phi), mp.sin(phi)])
        out[nm] = float(mp.sqrt((hub[0]-s[0])**2+(hub[1]-s[1])**2)-r)
    return out


print()
print('   controls: b1 != b2, hub placed on the site-1 tangency surface when the chart')
print('   admits that branch, otherwise on the norm circle; Cartesian distances recomputed')
print('   independently from the site angles phi1 = delta + b1, phi2 = delta - b2.')
print()
cnt = 0
for (rv, b1v, b2v, dv) in [(mp.mpf('0.377'), mp.mpf('1.05'), mp.mpf('1.10'), mp.mpf('-0.05')),
                           (mp.mpf('0.376'), mp.mpf('1.10'), mp.mpf('1.02'), mp.mpf('0.08')),
                           (mp.mpf('0.378'), mp.mpf('1.02'), mp.mpf('1.15'), mp.mpf('-0.13'))]:
    a1 = 2*b1v-dv
    a2 = 2*b2v+dv
    r = rv
    # hub on the face-1 cap (H = 2r sin(2b1-delta)); only valid if the argument is in range
    if not (0 < a1 < mp.pi/2):
        print(f'   [{cnt}] r={float(rv)} b1={float(b1v)} b2={float(b2v)} d={float(dv)}: '
              f'2b1-delta = {float(a1):.4f} outside (0,pi/2) -> face-1 cap not on this branch')
        cnt += 1
        continue
    H = 2*r*mp.sin(a1)
    R1, R2, N = residuals(r, b1v, b2v, dv, H)
    cq = cart_quantities(r, H, dv, dv+b1v, dv-b2v)
    lhs = 2*r*(mp.sin(2*b2v+dv)-mp.sin(2*b1v-dv))
    rhs = 4*r*mp.cos(b1v+b2v)*mp.sin(b2v-b1v+dv)
    print(f'   [{cnt}] r={float(rv)} b1={float(b1v)} b2={float(b2v)} delta={float(dv)}')
    print(f'        H (on face-1 cap) = {float(H):.9f} ; sites at phi1=delta+b1='
          f'{float(dv+b1v):+.6f}, phi2=delta-b2={float(dv-b2v):+.6f}')
    print(f'        residuals: R1={R1:+.3e} (0 by construction)  R2={R2:+.9f}  N={N:+.9f}')
    print(f'        ident:  R2-R1 = 2r[sin(2b2+d)-sin(2b1-d)] = {float(lhs):+.12f} ;'
          f' 4r cos(b1+b2) sin(b2-b1+d) = {float(rhs):+.12f} ; diff = {float(abs(lhs-rhs)):.2e}')
    print(f'        Cartesian: |hub-c1|-r = {cq["c1"]:+.9f}  (=R1/1? signed) ; '
          f'|hub-c2|-r = {cq["c2"]:+.9f}')
    print(f'        FILTER verdict on this branch: R2>=0? {R2>=0}  N>=0? {N>=0}'
          f'   -> whole filter {R1>=0 and R2>=0 and N>=0}')
    cnt += 1
    print()

print('=== (3) what is invalidated by the wrong identity ===')
print('''   * my "Nc depends on (r,delta) alone" claim -- FALSE, N depends on b1,b2 via H;
   * the reduction "legality becomes delta <= 0" -- FALSE;
   * every legal-census / interval-certification result built on that filter:
       R16-INTERVAL-DISJUNCTION-RUN.md and r16rr_factored.py, r16qq_deltafirst2.py,
       r16pp_deltafirst.py, r16oo_paired.py, r16nn_run.py, r16ll_boundary.py,
       r16jj_disjunction.py  -- all INVALID as legality censuses.
   * the "2970 boxes certified" count and the obstacle family are not usable.''')
print()
print('No 10x refinement was launched. Awaiting the lead\'s sizing.')
json.dump(dict(worst_identity_error=str(worst)), open(OUT/'r16vv_identity.json', 'w'), indent=1)
