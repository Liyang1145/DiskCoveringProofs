"""cline2-coupled-factors R16e: classify the constraint active at each maximum.

The three active constraints are:
  alpha1 := 2r sin(b1+A) - H      (face-1 cap;  alpha1 >= 0)
  alpha2 := 2r sin(b2+B) - H      (face-2 cap;  alpha2 >= 0)
  beta   := 2 s cos(delta) H - H^2 - 2 r (1-r)   (norm disk;  beta >= 0)
with A = b1-delta, B = b2+delta, s = sqrt(1-r^2).  The hub objective's delta-derivative
along a branch can vanish in three ways:
   dV/ddelta = 0 with  H = 2r  (the beta - H^2 = 0 stationarity, seen on the norm branch)
   dV/ddelta = 0 with  alpha1 = 0
   dV/ddelta = 0 with  alpha2 = 0
(endpoint maxima at delta = b1 = ridge, delta = -b2, or a feasibility boundary).
This script labels which one is active at the reported maximum and at the interior root,
so the reduction claim can be stated precisely rather than numerically.
"""
import numpy as np, json, math, sys
from pathlib import Path
P = Path(__file__).parent
sys.path.insert(0, str(P))
import r16b_analytic_deriv as A

OUT = P / 'out'


def constraints(delta, r, b1, b2, H):
    s = math.sqrt(1.0-r*r)
    Aa = b1-delta; Bb = b2+delta
    alpha1 = 2*r*math.sin(b1+Aa)-H
    alpha2 = 2*r*math.sin(b2+Bb)-H
    beta = 2*s*math.cos(delta)*H - H*H - 2*r*(1.0-r)
    return alpha1, alpha2, beta


def classify_point(delta, r, b1, b2, j):
    rv = A.value_and_deriv(delta, r, b1, b2, j)
    if rv is None:
        return None
    s = math.sqrt(1.0-r*r)
    if j == 0:
        H = 2*r*math.sin(2*b1-delta)
    elif j == 1:
        H = 2*r*math.sin(2*b2+delta)
    else:
        rad = (1.0-r)**2 - s*s*math.sin(delta)**2
        if rad < 0:
            return None
        H = s*math.cos(delta) + (1 if j == 2 else -1)*math.sqrt(rad)
    a1, a2, be = constraints(delta, r, b1, b2, H)
    TOL = 1e-7
    tags = []
    if abs(a1) < TOL:
        tags.append('face1-cap')
    if abs(a2) < TOL:
        tags.append('face2-cap')
    if abs(be) < TOL:
        tags.append('norm-disk')
    if abs(delta-b1) < TOL:
        tags.append('ridge delta=b1')
    if abs(delta+b2) < TOL:
        tags.append('delta=-b2')
    if abs(H-2*r) < TOL:
        tags.append('H=2r')
    return dict(V=rv[0], dV=rv[1], H=H, alpha1=a1, alpha2=a2, beta=be, tags=tags)


print('=== classification at the argmax of each profile (from r16d) ===')
rows = json.loads((OUT/'r16d_roots.json').read_text())
import collections
tags_at_max = collections.Counter()
tags_at_root = collections.Counter()
for row in rows:
    cl = classify_point(row['d_at_vmax'], row['r'], row['b1'], row['b2'], row['j'])
    if cl is None:
        continue
    key = tuple(sorted(cl['tags']))
    tags_at_max[(row['j'], key)] += 1
    for root in row['roots']:
        cr = classify_point(root, row['r'], row['b1'], row['b2'], row['j'])
        if cr:
            tags_at_root[(row['j'], tuple(sorted(cr['tags'])))] += 1
print('tags at the profile argmax, by (branch, active set):')
for k in sorted(tags_at_max):
    print(f'   j={k[0]}  {k[1]} : {tags_at_max[k]}')
print('\ntags at the interior derivative roots (branch 3), by active set:')
for k in sorted(tags_at_root):
    print(f'   j={k[0]}  {k[1]} : {tags_at_root[k]}')

print('\n=== the exact identity at delta = b1 (ridge) ===')
for (r, b1, b2) in [(0.375, 1.0, 1.0), (0.375, 1.1, 1.05), (0.38, 1.0, 1.0),
                    (0.38, 1.05, 1.10)]:
    cl = classify_point(b1, r, b1, b2, 0)
    print(f'   r={r} b1={b1} b2={b2}, branch0 at delta=b1: {None if cl is None else {k: round(v,12) if isinstance(v,float) else v for k,v in cl.items()}}')

print('\n=== the tangent point H = 2r on the norm-positive branch ===')
for (r, b1, b2) in [(0.375, 1.0, 1.0), (0.38, 1.0, 1.0), (0.375, 1.1, 1.05)]:
    s = math.sqrt(1-r*r)
    # solve H = 2r on the + branch: 2r = s cos d + sqrt((1-r)^2 - s^2 sin^2 d)
    lo, hi = -b2, b1
    f = lambda d: (s*math.cos(d)+math.sqrt(max((1-r)**2 - s*s*math.sin(d)**2, 0.0))) - 2*r
    root = None
    xs = np.linspace(lo, hi, 20001)
    for k in range(len(xs)-1):
        if f(xs[k])*f(xs[k+1]) < 0:
            a, b = xs[k], xs[k+1]
            for _ in range(80):
                m = 0.5*(a+b)
                if f(a)*f(m) <= 0:
                    b = m
                else:
                    a = m
            root = 0.5*(a+b)
            break
    if root is None:
        print(f'   r={r} b1={b1} b2={b2}: no H=2r crossing on the + branch')
        continue
    cl = classify_point(root, r, b1, b2, 3)
    print(f'   r={r} b1={b1} b2={b2}: H=2r at delta={root:.8f}; '
          f'dV/ddelta={cl["dV"]:+.3e} (zero iff stationarity holds); '
          f'alpha1={cl["alpha1"]:+.3e} alpha2={cl["alpha2"]:+.3e} beta={cl["beta"]:+.3e}')
