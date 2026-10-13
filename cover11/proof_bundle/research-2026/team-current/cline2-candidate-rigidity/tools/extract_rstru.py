"""Extract the exact closure radius R_stru from the lead's closure system.

The lead's system (lead/q0_exact_closure_radius.py) uses variables
    x = [ 33 face angles, 9 switch angles b_i, 20 log-radii, log R ]
with 13 angle-sum equalities, 21 edge matching rows (log-sine ratios) and 9 boundary
cyclic closure rows.  His x0 (saved in lead/q0_exact_closure_radius.json) is the candidate
lift; his rank is 41 of 43 rows, nullity 22.

Kernel elimination: log R is the last variable; row i and row k have identical columns
wherever the angle pattern A == B.  We do not need the log radii: instead we read off the
value of R implied by his x (exp(x[62])) and compare it with the numbers of the certified
object and with a direct covering-radius evaluation of the reconstructed centres.

This is calibration: no certificate.
"""
import json, io, math
import numpy as np
from pathlib import Path
from mpmath import mp, mpf, mpmathify, exp, sqrt, pi, atan2, acos, nstr

mp.dps = 40
ROOT = Path(__file__).resolve().parents[4]
LEAD = ROOT / 'research-2026' / 'team-current' / 'lead'
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
L = json.load(io.open(LEAD / 'q0_exact_closure_radius.json', encoding='utf-8-sig'))
T = json.load(io.open(LEAD / 'q0_closure_tangent.json', encoding='utf-8-sig'))

x = L['x0']
print('lead x0 length =', len(x))
print('exponentiated R from x0[62] = %s' % nstr(exp(mpf(x[62])), 30))
print('lead candidate_radius          = %s' % nstr(mpf(L['candidate_radius']), 30))
print('certified interval lo          = %s' % D['certified_interval']['lo'][:48])
print('certified interval hi          = %s' % D['certified_interval']['hi'][:48])
print()
print('lead runs:')
for r in L['runs']:
    print('  trial %d success=%s R=%s active_radii=%d residual=%.3e min_ineq=%.3e'
          % (r['trial'], r['success'], nstr(mpf(r['radius']), 24), r['active_radii'],
             r['all_eq_residual'], r['min_ineq']))
print()
print('tangent analysis:')
print('  active indices   :', T['active_indices'])
print('  inactive radii   :', T['inactive_radii'])
print('  constraint rank  :', T['constraint_rank_numeric'], 'tangent dim', T['tangent_dimension_numeric'])
print('  multipliers      :', [round(v, 6) for v in T['active_multipliers']])
print('  Hessian eigs     :', T['tangent_hessian_eigenvalues_numeric'])
print('  dR components    :', T['tangent_R_components'])
print('  stationarity res :', T['stationarity_residual'])
print()
# R_stru best estimate: min over runs, and compare with UB*
rs = [mpf(r['radius']) for r in L['runs'] if r['success']]
hi = mpmathify(D['certified_interval']['hi'])
lo = mpmathify(D['certified_interval']['lo'])
print('min over lead runs of R            = %s' % nstr(min(rs), 30))
print('certified lo / hi                  = %s / %s' % (nstr(lo, 30), nstr(hi, 30)))
print('(lead min R) - hi                  = %s' % nstr(min(rs) - hi, 6))
print('(lead min R) - lo                  = %s' % nstr(min(rs) - lo, 6))
print()
print('=== exact-arithmetic check of the tight points at the SAVED object ===')
C = [(mpf(int(a)) / mpf(10) ** 17, mpf(int(b)) / mpf(10) ** 17) for a, b in D['centers_scaled_1e17']]
print('Delaunay graph of the saved object vs q0_graphs[2] (k=4, hub degrees 7,6):')
try:
    from scipy.spatial import Delaunay
    Cf = np.array([[float(a), float(b)] for a, b in C])
    faces = {tuple(sorted(f)) for f in Delaunay(Cf).simplices}
    G = json.load(io.open(LEAD / 'q0_graphs.json', encoding='utf-8-sig'))
    for gi, g in enumerate(G):
        tgt = {tuple(sorted(f)) for f in g['faces']}
        print('   graph %d (span=%d): match=%s' % (gi, g['span'], tgt == faces))
except Exception as e:
    print('   Delaunay check failed:', e)
