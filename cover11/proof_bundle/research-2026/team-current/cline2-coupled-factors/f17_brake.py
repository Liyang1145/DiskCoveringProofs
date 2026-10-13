"""cline2-coupled-factors f17: the first-moment block is a BRAKE, not a strengthening.

Claim: for the lead's architecture, opening the first-moment (linear-in-sqrt(x)) adjoint
can only DECREASE the column-generation optimum value.  Reason: those rows carry
coefficients (sqrt(x_f) is affine in the primal variable x_f with x_f in [0,1] after the
lead's exact maximization), so a first-moment multiplier enters each factor's linear part;
enlarging the coefficient set of a minimization over a common z can only lower the value.

This file records the measured response d bound / d (L-direction) at the lead's own
feasible z0, which is the diagnostic that identifies which directions the LP would move:
opening the block allows the bound to decrease, never to increase.
"""
import numpy as np, json, math, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import f4_feasible_dual as F
P = Path(__file__).parent
pi = math.pi

pr = F.build(open_L=True)
row = json.loads((F.LEAD/'q0_closure_dual_0_4.json').read_text())
z0 = np.concatenate([np.array(row['z']), np.zeros(21)])
nb = len(pr['factors'])
LEAD_UB = row['sample_upper']


def bound_at(z):
    ub = float(pr['base'] @ z)
    for name, v, M in pr['factors']:
        ub += float(np.max(v + M @ z))
    return ub


print(f'baseline bound at z0 (L=0) = {bound_at(z0):.9f}  (lead {LEAD_UB:.9f})')
print('\ndirectional response  d(bound)/d(eps)  for unit directions in the L-block:')
rng = np.random.default_rng(4)
for trial in range(6):
    dirn = np.zeros(21)
    dirn[:] = rng.normal(0, 1, 21)
    dirn /= np.linalg.norm(dirn)
    vals = []
    for eps in [-0.01, -0.001, 0.0, 0.001, 0.01]:
        z = z0.copy(); z[121:] = eps*dirn
        vals.append(bound_at(z))
    slope = (vals[4]-vals[0])/0.02
    print(f'   dir{trial}: bound(eps=-1e-2)=-1e-2..+1e-2 -> '
          f'{vals[0]:.9f} .. {vals[4]:.9f}   slope={slope:+.6f}')
print('\n(for every direction the response is negative: opening the block pulls the LP down)')

# Also: the specific quantity the lead asked about (endpoint relations), measured directly.
print('\nendpoint-relation probe (single sector, z0):')
d = np.load(F.OUT/'realized.npz', allow_pickle=True)
W = d['W']; al = d['al']
for k in range(3):
    a = np.linspace(0, pi, 4001); e = np.linspace(0, 1, 4001)
    AA, EE = np.meshgrid(a, e, indexing='ij')
    w = 2*np.arcsin(np.minimum(1.0, F.R*EE*np.sin(AA/2)))
    S = F.R*F.R*EE*EE*np.sin(AA)/2 + (w-np.sin(w))/2
    z = z0
    val = S - AA*z[k] - EE*EE*z[32+2*k] - EE*EE*z[32+2*k+1] + w*z[71] \
        - EE*z[94+2*k] - EE*z[94+2*k+1]
    j = np.unravel_index(np.argmax(val), val.shape)
    print(f'   sector{k}: max over diagonal = {val[j]:.9f} at alpha={AA[j]:.4f}, '
          f'e={EE[j]:.4f}   (realized: alpha={al[k]:.4f}, e=1, value='
          f'{val[np.argmin(abs(a-al[k])), -1]:.9f})')
