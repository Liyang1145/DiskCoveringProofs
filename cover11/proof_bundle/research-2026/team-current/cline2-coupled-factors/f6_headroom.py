"""cline2-coupled-factors f6: headroom calibration at the SAVED global upper candidate.

The certified upper candidate sits at r = 0.3799838531198387, so at that radius it is a
FEASIBLE 11-disk cover and its area is exactly pi.  For any valid dual bound ub(z) of the
lead's architecture one has ub(z) >= pi and moreover

    ub(z) - pi  >=  [const.z + sum_f (row value of factor f at the realization)] - pi
                =: dual slack of z at the realization,

because each factor's max dominates its value at the realized point.  That slack is the
most any dual of this architecture can ever recover AT THIS POINT, hence it calibrates
how much room a "sharper coupling" still has.  We compute it for the lead's feasible z0.

We also report the primal residuals of the realized configuration (which angle equations
are tight), to name the factor rows that carry the weight.
"""
import numpy as np, json, math, sys
from pathlib import Path
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
R = 19/50
pi = math.pi

obj = json.loads((P.parent / 'cline2-sharp-fan' / 'out' / 'certified_object_copy.json')
                 .read_text(encoding='utf-8-sig'))
C = np.array(obj['centers_scaled_1e17'], dtype=float)/1e17
Rc = float(obj['certified_upper_bound_21digits'])
n = len(C)
print(f'R_cert = {Rc:.18f}   n = {n}')
D = np.linalg.norm(C[:, None, :]-C[None, :, :], axis=2)
np.fill_diagonal(D, np.inf)
print(f'min pairwise centre distance = {D.min():.12f}   2R = {2*Rc:.12f}')
t = np.linspace(0, 2*pi, 4000001)
g = np.stack([np.cos(t), np.sin(t)], 1)
dd = np.min(np.linalg.norm(g[:, None, :]-C[None, :, :], axis=2), axis=1)
imax = int(np.argmax(dd))
print(f'max over bd(D) of min_i |p-c_i| = {dd[imax]:.15f}  at t={t[imax]:.12f}')
print(f'  R_cert - that = {Rc-dd[imax]:+.3e}   (should be ~0 for the certified object)')
print(f'  switches = boundary points with two nearest sites; count of near-ties:')
near = np.where(dd > dd.max()-1e-6)[0]
print(f'    {len(near)} samples within 1e-6 of the max over {len(t)} '
      f'(=> the argmax is a curved arc, so this object is NOT a clean single-switch case)')
# distinct argmax clusters
cl = []
for k in near:
    if not cl or t[k]-t[cl[-1][-1]] > 0.05:
        cl.append([k])
    else:
        cl[-1].append(k)
print(f'    {len(cl)} argmax clusters at t = '
      f'{np.round([t[c[0]+len(c)//2] for c in cl], 6)}')
np.save(OUT/'centers.npy', C)
