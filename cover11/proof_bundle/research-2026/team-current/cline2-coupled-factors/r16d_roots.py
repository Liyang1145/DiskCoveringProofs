"""cline2-coupled-factors R16d: definitive derivative/root structure on the boundary branches.

Setup (lead's chart, C861/C862), with the least-upper-bound structure made explicit:

  On the face-1 boundary, V(delta) is EXACTLY phi1 = b1 and L1 = 2r sinA (chart identity),
  so the branch is monotone by direct computation (dV/ddelta > 0 on the whole stated range,
  minimum measured slope +0.1627).  Same for the face-2 branch.

  On the norm boundary, with q(delta) = (1-r)^2 - s^2 sin^2 delta, H = s cos(delta) +- sqrt(q),
  we have d/dH [H^2 - 2 s cos(delta) H + 2 r (1-r)] = 2H - 2 s cos(delta) = 2H - 2H0 = +-2 sqrt(q),
  i.e. the norm constraint is STRICTLY monotone in H (increasing for the + branch, decreasing
  for the - branch).  Hence on the norm curve the objective's delta-derivative can only vanish
  where the derivative along H vanishes, which is a single scalar condition per branch.

This script:
  1. refines every derivative sign change of every branch to high precision (bounded work),
  2. classifies each acceptable sub-interval's maximum as endpoint / interior root,
  3. reports whether interior roots ever occur and, when they do, at which H they sit.
"""
import numpy as np, json, math, sys
from pathlib import Path
P = Path(__file__).parent
sys.path.insert(0, str(P))
import r16b_analytic_deriv as A

OUT = P / 'out'


def classify(r, b1, b2, j, n0=4001, iters=70):
    lo, hi = -b2, b1
    ds = np.linspace(lo, hi, n0)
    vals = [A.value_and_deriv(d, r, b1, b2, j) for d in ds]
    ok = [v is not None for v in vals]
    if not any(ok):
        return None
    # collect connected admissible runs
    runs = []
    k = 0
    while k < len(ds):
        if ok[k]:
            s0 = k
            while k+1 < len(ds) and ok[k+1]:
                k += 1
            runs.append((s0, k))
        k += 1
    rows = []
    for (s0, s1) in runs:
        if s1 <= s0:
            continue
        d0, d1 = ds[s0], ds[s1]
        # refine the two run endpoints to the feasibility boundary (bisection)
        def feasible(d):
            return A.value_and_deriv(d, r, b1, b2, j) is not None
        a, b = d0, ds[max(s0-1, 0)]
        if not feasible(b):
            for _ in range(iters):
                m = 0.5*(a+b)
                if feasible(m):
                    a = m
                else:
                    b = m
            d0r = a
        else:
            d0r = d0
        a, b = d1, ds[min(s1+1, len(ds)-1)]
        if not feasible(b):
            for _ in range(iters):
                m = 0.5*(a+b)
                if feasible(m):
                    a = m
                else:
                    b = m
            d1r = a
        else:
            d1r = d1
        # scan for derivative sign changes inside [d0r, d1r] and refine
        dd = np.linspace(d0r, d1r, max(200, n0//4))
        vv = [A.value_and_deriv(d, r, b1, b2, j) for d in dd]
        roots = []
        for k in range(len(dd)-1):
            if vv[k] is None or vv[k+1] is None:
                continue
            f0 = vv[k][1]; f1 = vv[k+1][1]
            if f0 == 0:
                roots.append(dd[k]); continue
            if f0*f1 < 0:
                lo2, hi2 = dd[k], dd[k+1]
                for _ in range(iters):
                    m = 0.5*(lo2+hi2)
                    vm = A.value_and_deriv(m, r, b1, b2, j)
                    if vm is None:
                        break
                    if (vm[1] > 0) == (f0 > 0):
                        lo2 = m
                    else:
                        hi2 = m
                roots.append(0.5*(lo2+hi2))
        # candidates: run endpoints and roots
        cand = [d0r, d1r]+roots
        best = None
        for d in cand:
            rv = A.value_and_deriv(d, r, b1, b2, j)
            if rv is None:
                continue
            if best is None or rv[0] > best[0]:
                best = (rv[0], d)
        # is the best a root (interior critical) rather than a run endpoint?
        at_end = min(abs(best[1]-d0r), abs(best[1]-d1r))
        rows.append(dict(r=r, b1=b1, b2=b2, j=j, run=(float(d0r), float(d1r)),
                         vmax=float(best[0]), d_at_vmax=float(best[1]),
                         n_roots=len(roots), roots=[float(x) for x in roots],
                         dist_to_end=float(at_end),
                         interior_root=bool(len(roots) and at_end > 1e-6)))
    return rows


print('=== refined root/interval structure ===')
allrows = []
for r in [0.375, 0.3775, 0.38]:
    bmax = math.acos(r)
    for b1 in np.linspace(1.0, bmax, 5):
        for b2 in np.linspace(1.0, bmax, 5):
            for j in (0, 1, 2, 3):
                rs = classify(r, b1, b2, j)
                if rs:
                    allrows.extend(rs)
print(f'profiles: {len(allrows)}')
import collections
print('by (j, number of roots):',
      dict(collections.Counter((row['j'], row['n_roots']) for row in allrows)))
print('by (j, number of admissible runs):',
      dict(collections.Counter((row['j'], len({tuple([row['run'][0]]) for _ in [0]})) for row in allrows)))
inter = [row for row in allrows if row['interior_root']]
print(f'\nsub-interval maxima that are INTERIOR critical points: {len(inter)} of {len(allrows)}')
for row in inter[:10]:
    print(f'   r={row["r"]} b1={row["b1"]:.4f} b2={row["b2"]:.4f} j={row["j"]} '
          f'run=[{row["run"][0]:.5f},{row["run"][1]:.5f}] Vmax={row["vmax"]:.6f} at '
          f'delta={row["d_at_vmax"]:.6f} (dist to run end {row["dist_to_end"]:.2e}, '
          f'roots={len(row["roots"])})')
# where do the maxima sit overall?
at_end = sum(1 for row in allrows if not row['interior_root'])
print(f'\nmaxima at a run endpoint (feasibility boundary): {at_end} of {len(allrows)}')
json.dump(allrows, open(OUT/'r16d_roots.json', 'w'), indent=1)
print('saved out/r16d_roots.json')
