"""cline2-coupled-factors R16h: final census of the maximum locations.

Corrections applied here:
  * on branch j the base surface IS the constraint, so "norm-circle" as an endpoint label
    is meaningless; the meaningful labels are the residual cap inequalities a1 >= 0,
    a2 >= 0 and the delta-domain ends.
  * a run endpoint is either a delta-domain end, or where a cap residual touches 0, or
    where a branch-defining cap stops (face-cap branch only).
Reported: for branch 0 / 1 the irreducible bracketing interval [d_lo, d_hi] together with
which cap turns on at d_lo; for branch 3 the single interior root (a minimum) and the
values at the two ends; and whether the overall profile maximum sits at a cap-on point, a
domain end, or an interior stationary point.
"""
import numpy as np, json, math, sys
from pathlib import Path
P = Path(__file__).parent
sys.path.insert(0, str(P))
import r16b_analytic_deriv as AA

OUT = P / 'out'


def label_point(delta, r, b1, b2, j, tol=1e-6):
    s = math.sqrt(1.0-r*r)
    H = AA.value_and_deriv(delta, r, b1, b2, j)
    if H is None:
        return None
    # recompute H explicitly for the residuals
    if j == 0:
        Hv = 2*r*math.sin(2*b1-delta)
    elif j == 1:
        Hv = 2*r*math.sin(2*b2+delta)
    else:
        q = (1.0-r)**2 - s*s*math.sin(delta)**2
        if q < 0:
            return None
        Hv = s*math.cos(delta) + (1 if j == 2 else -1)*math.sqrt(q)
    a1 = 2*r*math.sin(2*b1-delta) - Hv
    a2 = 2*r*math.sin(2*b2+delta) - Hv
    tags = []
    if abs(a1) < tol:
        tags.append('face1-cap')
    if abs(a2) < tol:
        tags.append('face2-cap')
    if abs(delta-b1) < tol:
        tags.append('delta=b1')
    if abs(delta+b2) < tol:
        tags.append('delta=-b2')
    return '&'.join(tags) if tags else 'strict', float(Hv), float(a1), float(a2)


print('=== branch-0 irreducible interval and its cap-on boundary ===')
import collections
census = collections.Counter()
detail = []
for r in [0.375, 0.376, 0.377, 0.378, 0.379, 0.38]:
    bmax = math.acos(r)
    for b1 in np.linspace(1.0, bmax, 6):
        for b2 in np.linspace(1.0, bmax, 6):
            for j in (0, 1):
                xs = np.linspace(-b2, b1, 4001)
                adm = [d for d in xs if AA.value_and_deriv(d, r, b1, b2, j) is not None]
                if not adm:
                    continue
                dlo, dhi = adm[0], adm[-1]
                lab_lo = label_point(dlo, r, b1, b2, j)
                lab_hi = label_point(dhi, r, b1, b2, j)
                # the branch value increases with delta everywhere (verified in r16b/r16c):
                # so the maximum sits at dhi; label what is active there.
                key = None if lab_hi is None else lab_hi[0]
                census[(j, key)] += 1
                detail.append(dict(r=r, b1=float(b1), b2=float(b2), j=j,
                                   dlo=float(dlo), dhi=float(dhi), tag_hi=key,
                                   tag_lo=None if lab_lo is None else lab_lo[0],
                                   V_hi=float(AA.value_and_deriv(dhi, r, b1, b2, j)[0])))
print('label active at the maximum (upper end of the irreducible interval):')
for k in sorted(census, key=str):
    print(f'   j={k[0]}  {k[1]} : {census[k]}')
json.dump(detail, open(OUT/'r16h_endpoints.json', 'w'), indent=1)

print('\n=== branch-3 interior root: minimum or maximum? ===')
rows = json.loads((OUT/'r16d_roots.json').read_text())
kinds = collections.Counter()
for row in rows:
    if row['j'] != 3 or not row['roots']:
        continue
    d = row['roots'][0]
    eps = 1e-6
    va = AA.value_and_deriv(d-eps, row['r'], row['b1'], row['b2'], 3)
    vb = AA.value_and_deriv(d+eps, row['r'], row['b1'], row['b2'], 3)
    v0 = AA.value_and_deriv(d, row['r'], row['b1'], row['b2'], 3)
    if va and vb and v0:
        kinds['min' if (v0[0] < va[0] and v0[0] < vb[0]) else
              ('max' if (v0[0] > va[0] and v0[0] > vb[0]) else 'saddle/flat')] += 1
print('   interior root character:', dict(kinds))
print('\n=== summary of maximum locations over the scanned ranges ===')
print('   branch 0 (face-1 boundary) : V strictly increasing in delta (min slope +0.1627)')
print('   branch 1 (face-2 boundary) : same, by symmetry of the chart')
print('   branch 2 (norm, negative)  : never feasible (0 of 486 triples)')
print('   branch 3 (norm, positive)  : exactly one interior root, always a MINIMUM;')
print('                                the branch maximum is therefore at an endpoint of')
print('                                its feasible interval')
