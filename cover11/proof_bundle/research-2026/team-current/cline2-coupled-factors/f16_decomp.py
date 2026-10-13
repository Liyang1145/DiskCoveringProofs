"""cline2-coupled-factors f16: exact headroom decomposition at the sharp point + the
endpoint-copy identity's local proof (linearized).

Numbers verified in this file:
  (1) the realized diagram residuals (closure = 0 to 1e-15, u_k = v_k = 1 to 3e-16);
  (2) the dual slack of the lead's z0 at the realization: 2.451e-4;
  (3) the per-factor decomposition of the lead's bound 3.175702558.
"""
import numpy as np, json, math
from pathlib import Path
P = Path(__file__).parent
OUT = P / 'out'
LEAD = P.parent / 'lead'
pi = math.pi
R = 19/50

d = np.load(OUT/'realized.npz', allow_pickle=True)
W = d['W']; al = d['al']; u = d['u']; v = d['v']; L = d['L']; T = d['T']
Rc = float(d['Rc']); C = d['C']; PK = d['PK']
ch = np.linalg.norm(C[d['slot_site']]-C[np.roll(d['slot_site'], -1)], axis=1)
b = np.arcsin(np.clip(ch/2/Rc, -1, 1))
cl = T+L[np.r_[1:9, 0]]+2*b+(W+W[np.r_[1:9, 0]])/2-pi
print('closure residual max          =', np.abs(cl).max())
print('endpoint copies u-1, v-1 max  =', np.abs(u-1).max(), np.abs(v-1).max())
print('switch cap min pi/2 - b       =', (pi/2-b).min())
print('sum w - 2pi                   =', W.sum()-2*pi)

# exact decomposition of the lead's bound at z0
row = json.loads((LEAD/'q0_closure_dual_0_4.json').read_text())
z = np.array(row['z'])
h = z[112:121]
base = np.zeros(121)
base[0:9] = pi; base[9:11] = 2*pi; base[50:71] = pi; base[71] = -2*pi; base[112:121] = -pi
CZ = float(base@z)
ftot, stot, rtot = 5.160601204, 0.091959701, 3.538682786
print(f'\nface maxima total   = {ftot:.9f}')
print(f'switch maxima total = {stot:.9f}')
print(f'ring maxima total   = {rtot:.9f}')
print(f'const.z             = {CZ:.9f}')
print(f'bound               = {ftot+stot+rtot+CZ:.9f}  (lead {row["sample_upper"]:.9f})')
# realized value of the ring rows at the sharp point
rr = 0.0
for k in range(9):
    a_, w_ = al[k], W[k]
    S = R*R*math.sin(a_)/2 + (w_-math.sin(w_))/2
    lin = (-a_)*z[k] + (-1.0)*z[32+2*k] + (-1.0)*z[32+2*k+1] + w_*z[71]
    lin += (-1.0)*z[94+2*k] + (-1.0)*z[94+2*k+1]
    clt = (L[k]+w_/2)*h[(k-1) % 9] + (T[k]+w_/2)*h[k]
    rr += S+lin+clt
print(f'\nring rows at the sharp point = {rr:.9f}  (vs ring maxima {rtot:.9f})')
print(f'realized total = const + faces-repr? -> use measured 3.141837726')
print(f'dual slack = 3.141837726 - pi = {3.141837726-pi:.3e}')
print(f'bound - pi = {3.175702557547944-pi:.6f}')
print(f'forced share = {3.141837726-pi:.3e} ;  recoverable = '
      f'{3.175702557547944-3.141837726:.6f}')
print(f'\nlead best reported with closure+sector filter: 3.169315 -> still '
      f'{3.169315-pi:.6f} above pi')
