"""cline2-coupled-factors f29: corrected dual-at-candidate evaluation (definitive).

Uses the lead's own machinery (q0_exact_closure_radius.py) so there is no second assembly
to get wrong, and evaluates the lead's scalar dual identity at the saved candidate:

    D(z, candidate) = area + z[50:71].slack + z[71]*(sum ws - 2pi) + z[112:].cls

with `area = pi` on the candidate.  The script reports
  (a) the two radius ratios that were being mixed,
  (b) sum(ws) - 2pi and the closure residual cls on the candidate,
  (c) D - pi, i.e. the amount the dual subtracts from pi at the candidate,
  (d) the same quantity with the closure multipliers scaled, to show which slack channel
      feeds the 0.0341 gap between pi and the sampled bound 3.175702558.
"""
import numpy as np, json, math, sys
from pathlib import Path
P = Path(__file__).parent
LEAD = P.parent / 'lead'
pi = math.pi

src = (LEAD/'q0_exact_closure_radius.py').read_text()
head = src.split('res=ceq(x0)')[0]
ns = {'__file__': str(LEAD/'q0_exact_closure_radius.py'), '__name__': 'q0mod'}
exec(head, ns)
faces = ns['faces']; edges = ns['edges']; x0 = np.array(ns['x0'])
als, ws, cls, area = ns['calc'](x0)
Rc = 0.379983853119838733
Rr = 0.38
ys_full = np.exp(x0[42:62]+x0[-1])
print(f'(a) switch radius in absolute units: rho_switch = {ys_full[11]:.12f}')
print(f'    rho_switch/R          = {ys_full[11]/Rr:.12f}   (in the R=19/50 domain)')
print(f'    (rho_switch/R_cert)^2 = {(ys_full[11]/Rc)**2:.12f}   <- what f9 used, WRONG')
print(f'    (rho_switch/R)^2      = {(ys_full[11]/Rr)**2:.12f}   <- corect, equals max_normalized_radius in the lead json')
print(f'    squared-standardised max radius = {max(ys_full/Rr)**2:.12f}')
print(f'(b) area = {area:.15f}, pi = {pi:.15f}, area - pi = {area-pi:+.3e}')
print(f'    sum ws - 2pi = {sum(ws)-2*pi:+.6e}')
print(f'    closure residual cls = {np.round(cls, 12)}')
print(f'    pi - (A+B)@x0 = {pi-float(np.asarray((ns["A"]+ns["B"])@x0).ravel()[0]):+.6e}')

J = json.loads((LEAD/'q0_closure_dual_0_4.json').read_text())
z = np.array([float(f'{v:.9f}') for v in J['z']])
D = area + z[50:71]@(pi-(ns['A']+ns['B'])@x0) + z[71]*(sum(ws)-2*pi) + z[112:]@cls
print(f'(c) D = area + slack terms = {D:.15f}')
print(f'    D - pi = {D-pi:+.6e}')
print(f'    channels: z[50:71]@slack = {z[50:71]@(pi-(ns["A"]+ns["B"])@x0):+.6e}, '
      f'z[71]*(sum ws-2pi) = {z[71]*(sum(ws)-2*pi):+.6e}, '
      f'z[112:]@cls = {z[112:]@cls:+.6e}')
print(f'(d) sampled bound = {J["sample_upper"]:.9f};  gap to pi = '
      f'{J["sample_upper"]-pi:.6f}')
print(f'    D - pi (forced at the candidate) = {D-pi:+.6e}, so the recoverable part is '
      f'{J["sample_upper"]-D:.6f}')
h = z[112:]
print(f'    closure multipliers h = {np.round(h, 9)}  (sum {h.sum():.9f})')
print('    per-sector h-weighted closure residual h_i*c_i + h_(i-1)*c_(i-1):')
for i in range(9):
    print(f'      sector {i}: h[{i}]*cls = {h[i]*cls[i]:+.6e}, '
          f'h[{(i-1)%9}]*cls = {h[(i-1)%9]*cls[i]:+.6e}')
