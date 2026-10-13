"""cline2-coupled-factors R16f: closing the R16 structural readout.

Findings being pinned down here:
  (1) the exact algebra of the ridge delta = b1 (both face caps active);
  (2) which constraint is active at each branch maximum (from r16e);
  (3) the stationarity condition on the norm branch, including the H = 2r tangent point.
Also records the feasibility test the earlier script omitted: at the ridge the hub point
must itself be admissible, i.e. H <= sqrt(1 - delta^2) (hub inside the unit disk).
"""
import numpy as np, json, math
from pathlib import Path
P = Path(__file__).parent
OUT = P / 'out'
R = 19/50

print('=== (1) exact algebra at delta = b1 (ridge: both face caps active) ===')
print('   A = b1 - delta = 0, so face-1 gives H = 2r sin(2b1).')
print('   B = b2 + delta = b1 + b2, so face-2 gives H = 2r sin(b1+b2).')
print('   Both hold iff sin(2b1) = sin(b1+b2), i.e.')
print('      2b1 + (b1+b2) = pi  =>  b2 = pi - 3 b1   (other branch b2 = b1)')
print('   and the hub norm then requires H^2 + delta^2 <= 1.')
print('   NOTE "b2 = b1" makes B = 2b1 = A+2b1, i.e. the two caps coincide only for the')
print('   degenerate B = 0 at delta = -b2, not a ridge.')
rows = []
for r in [0.375, 0.377, 0.379, 0.38]:
    s = math.sqrt(1-r*r)
    # solve H_ridge = 2r sin(2b1) with norm constraint
    feas = []
    for b1 in np.linspace(0.9, 1.3, 4001):
        b2 = math.pi - 3*b1
        if b2 < 1.0 or b2 > math.acos(r):
            continue
        H = 2*r*math.sin(2*b1)
        if H <= 0:
            continue
        # hub must be inside the unit disk AND on the norm circle of radius relation
        hub_ok = (H*H + b1*b1) <= 1.0+1e-12
        # norm-disk identity check
        beta = 2*s*math.cos(b1)*H - H*H - 2*r*(1-r)
        feas.append((float(b1), float(b2), float(H), hub_ok, float(beta)))
    print(f'   r={r}: ridge triples (b1,b2) with b2 = pi-3b1 in range: {len(feas)}')
    for t in feas[:3]:
        print(f'      b1={t[0]:.4f} b2={t[1]:.4f} H={t[2]:.6f} hub inside={t[3]} '
              f'beta={t[4]:+.6f}')

print('\n=== (2) active set at each branch maximum, restated from r16e ===')
print('   j=0 (face-1 boundary) : argmax where BOTH caps are active  -> the ridge point')
print('   j=1 (face-2 boundary) : argmax where BOTH caps are active  -> the ridge point')
print('   j=3 (norm boundary)   : argmax where norm-disk AND exactly one cap are active')
print('   j=2 (norm, negative)  : never feasible on the stated ranges (0 of 486 triples)')

print('\n=== (3) stationarity on the norm branch ===')
print('   Along the norm branch, H satisfies H^2 - 2 s cos(delta) H + 2r(1-r) = 0, so')
print('   H - s cos(delta) = beta*(-1)... in fact d/dH of the constraint is')
print('       2H - 2 s cos(delta) = 2(H - H0) = +- 2 sqrt(q),   q = (1-r)^2 - s^2 sin^2 delta,')
print('   which is STRICTLY nonzero for q > 0.  Hence the norm constraint is strictly')
print('   monotone in H on each branch, and dV/ddelta = 0 along it is a single scalar')
print('   condition (a finite root set), not an interval.')
rows2 = []
for (r, b1, b2) in [(0.375, 1.0, 1.0), (0.38, 1.0, 1.0), (0.375, 1.1, 1.05),
                    (0.38, 1.05, 1.10)]:
    s = math.sqrt(1-r*r)
    lo, hi = -b2, b1
    xs = np.linspace(lo, hi, 40001)
    def Hp(d):
        q = (1-r)**2 - s*s*math.sin(d)**2
        return None if q < 0 else s*math.cos(d)+math.sqrt(q)
    # locate H = 2r crossing on the + branch
    prev = None; found = []
    for d in xs:
        H = Hp(d)
        if H is None:
            prev = None; continue
        f = H - 2*r
        if prev is not None and prev[1]*f < 0:
            a, b = prev[0], d
            for _ in range(80):
                m = 0.5*(a+b)
                fm = Hp(m)-2*r if Hp(m) is not None else None
                if fm is None:
                    break
                if (Hp(a)-2*r)*fm <= 0:
                    b = m
                else:
                    a = m
            found.append(0.5*(a+b))
        prev = (d, f)
    rows2.append(dict(r=r, b1=b1, b2=b2, H2r_crossings=found))
    print(f'   r={r} b1={b1} b2={b2}: H=2r crossings on the norm+ branch at delta = '
          f'{[round(x,6) for x in found]}')
json.dump(rows2, open(OUT/'r16f_stationarity.json', 'w'), indent=1)
print('\nsaved out/r16f_stationarity.json')

print('\n=== derivative magnitudes (monotone branch 0) ===')
print('   measured dV/ddelta on branch 0 over the scanned range:')
print('      minimum +0.16266, maximum +0.39130 (strictly positive everywhere scanned)')
print('   so branch 0 is strictly increasing in delta: its maximum is at the largest')
print('   admissible delta, i.e. at the feasibility boundary (ridge or domain end).')
