"""cline2-coupled-factors f27: root cause of the wrong 2.451e-4 and the corrected statement.

Root cause.  f9_slack.py computed each face's realized term as
      2*R*R*xr*sinA*sinB*sinC   with   R = 19/50  and  xr = (rho/R_cert)^2.
The correct normalization of the lead's dual is x = (rho/R_relax)^2 with the SAME R in the
prefactor, so the product must be rho^2 sinA sinB sinC.  Using (rho/R_cert) with R^2 instead
inflates every face term by (R/R_cert)^2 - 1 = 8.4987e-5 and every ring term likewise, which
is exactly the spurious 2.451e-4 that f9 reported.

Corrected statement: at the saved candidate realization the lead's dual has
       const.z0 + sum_f (row_f(z0))  =  pi   to 4.4e-16,
so the dual is TIGHT at the sharp point: there is no forced slack, and the whole
ub(z0) - pi = 0.0341100 is recoverable in principle by a coupling that excludes the dual's
unrealizable maxima.

This script prints the two evaluations side by side and the ratio diagnostic.
"""
import numpy as np, math
from pathlib import Path
P = Path(__file__).parent
OUT = P / 'out'
import sys
sys.path.insert(0, str(P))
import f26_redo_radii as F

R = F.R; RC = F.RC
print(f'R = {R:.12f}   R_cert = {RC:.18f}   (R/R_cert)^2 - 1 = {(R/RC)**2-1:+.6e}')
tot_ok, det_ok = F.realized_total(R)
tot_bad, det_bad = F.realized_total(RC)
print(f'\ncorrect normalization  x = (rho/R)^2      -> total = {tot_ok:.12f}  '
      f'(pi + {tot_ok-math.pi:+.3e})')
print(f'f9 normalization       x = (rho/R_cert)^2 -> total = {tot_bad:.12f}  '
      f'(pi + {tot_bad-math.pi:+.3e})')
print(f'difference = {tot_bad-tot_ok:+.6e}   <- this was the spurious "forced share"')
print('\nper-factor realized contributions under the correct normalization:')
for n, v, xv in det_ok:
    print(f'   {n:9s} {v: .9f}   (x or e^2 = {xv:.9f})')
print(f'\nsum of the 29 realized row values + const = {tot_ok:.12f}')
print('Reading: the dual attains pi exactly at this realization, i.e. it is a support '
      'functional of the area form evaluated at the candidate; the entire 0.0341100 gap to '
      'the sampled dual value is the cost of the dual taking its maxima at non-realizable '
      'points.')
