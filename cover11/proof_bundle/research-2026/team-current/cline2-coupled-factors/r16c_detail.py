"""cline2-coupled-factors R16c: detailed structure of the single sign change on branch 3,
and feasibility bookkeeping for all four branches.

Questions:
  (a) on branch j=3 (norm-positive) the derivative has exactly ONE sign change in every
      profile -- is that a maximum or a minimum, and where does it sit relative to the
      ridge (delta=b1) and to the branch's own feasibility boundary?
  (b) are branches j=1 and j=2 ever feasible inside the stated ranges (my scan found j=2
      empty and j=1 feasible only at the degenerate B=0 edge)?
  (c) does any branch attain its maximum strictly inside the delta domain
      (a "residual interior maximum" that would break the ridge-or-endpoint picture)?
"""
import numpy as np, json, math, sys
from pathlib import Path
P = Path(__file__).parent
sys.path.insert(0, str(P))
import r16b_analytic_deriv as A

OUT = P / 'out'


def admiss(r, b1, b2, j, n=6001):
    lo, hi = -b2, b1
    ds = np.linspace(lo, hi, n)
    ok = []
    for d in ds:
        rv = A.value_and_deriv(d, r, b1, b2, j)
        ok.append(None if rv is None else rv)
    idx = [i for i, v in enumerate(ok) if v is not None]
    if not idx:
        return None
    return ds, ok, idx


print('=== feasibility census over the stated ranges ===')
census = {0: 0, 1: 0, 2: 0, 3: 0}
tot = 0
for r in [0.375, 0.376, 0.377, 0.378, 0.379, 0.38]:
    bmax = math.acos(r)
    for b1 in np.linspace(1.0, bmax, 9):
        for b2 in np.linspace(1.0, bmax, 9):
            tot += 1
            for j in range(4):
                if admiss(r, b1, b2, j) is not None:
                    census[j] += 1
print(f'   of {tot} (r,b1,b2) triples: branches with a nonempty admissible set: {census}')

print('\n=== detailed branch-3 structure at representative triples ===')
rows = []
for (r, b1, b2) in [(0.375, 1.0000, 1.0000), (0.375, 1.0621, 1.0621),
                    (0.375, 1.1000, 1.0500), (0.378, 1.0500, 1.1000),
                    (0.380, 1.0000, 1.0000), (0.380, 1.1000, 1.0200)]:
    for j in (0, 3):
        ad = admiss(r, b1, b2, j)
        if ad is None:
            print(f'   r={r} b1={b1:.4f} b2={b2:.4f} j={j}: no admissible delta')
            continue
        ds, ok, idx = ad
        d = np.array([ds[i] for i in idx])
        v = np.array([ok[i][0] for i in idx])
        dv = np.array([ok[i][1] for i in idx])
        # sign changes of the derivative
        sgn = np.sign(dv)
        ch = [k for k in range(len(sgn)-1) if sgn[k] != sgn[k+1]]
        kinds = []
        for k in ch:
            nxt = dv[k+1]-dv[k]
            kinds.append('max' if dv[k] > 0 and dv[k+1] < 0 else
                         ('min' if dv[k] < 0 and dv[k+1] > 0 else '?'))
        vmax_i = int(np.argmax(v)); vmin_i = int(np.argmin(v))
        interior = (0 < vmax_i < len(v)-1)
        near_ridge = abs(d[vmax_i]-b1) < 1e-6
        near_lo = abs(d[vmax_i]-d[0]) < 1e-6
        rows.append(dict(r=r, b1=b1, b2=b2, j=j, dlo=float(d[0]), dhi=float(d[-1]),
                         n=len(d), vmax=float(v[vmax_i]), d_at_vmax=float(d[vmax_i]),
                         interior=bool(interior), at_ridge=bool(near_ridge),
                         at_lo=bool(near_lo), sign_changes=len(ch), kinds=kinds,
                         dv_endpoints=(float(dv[0]), float(dv[-1]))))
        print(f'   r={r} b1={b1:.4f} b2={b2:.4f} j={j}: delta in [{d[0]:.4f},{d[-1]:.4f}] '
              f'n={len(d)}')
        print(f'      Vmax={v[vmax_i]:.6f} at delta={d[vmax_i]:.6f}   '
              f'at_ridge(A=0)={near_ridge} at_lower_end={near_lo} interior={interior}')
        print(f'      dV at ends = ({dv[0]:.5f}, {dv[-1]:.5f})   sign changes={len(ch)} {kinds}')
print('\n=== summary of the max locations ===')
n_int = sum(1 for r in rows if r['interior'])
n_ridge = sum(1 for r in rows if r['at_ridge'])
n_lo = sum(1 for r in rows if r['at_lo'])
print(f'   profiles: {len(rows)}  interior maxima: {n_int}  at ridge (delta=b1): {n_ridge}  '
      f'at lower end: {n_lo}')
json.dump(rows, open(OUT/'r16c_detail.json', 'w'), indent=1)
print('\nsaved out/r16c_detail.json')
