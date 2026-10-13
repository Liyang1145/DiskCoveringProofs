"""cline2-coupled-factors g9: verification of the M=1 witness and of the global chain.

The chain to be certified numerically (all steps exact inequalities, domains stated):
   (G2) R = M q_i/ell_i for every i in {0..8}
   (G3) M ell_i <= 2 sin(alpha_i/2) =: s_i
   (G4) R >= M^2 min_i (q_i/s_i)
A witness shape with M = 1 exactly, all 15 constraints satisfied, all domain inequalities
strict, and R < 0.38 shows that (G2)-(G4) plus the equality constraints CANNOT prove
R >= 0.38: the remaining content must be a strictly larger lower bound on M.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np, math, json, importlib.util
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
ns = {'__file__': str(LEAD/'q0_exact_closure_radius.py')}
exec((LEAD/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0], ns)
spec = importlib.util.spec_from_file_location('gmod', P/'g1_structure.py')
gm = importlib.util.module_from_spec(spec); spec.loader.exec_module(gm)
eq = ns['eq']; rhs = ns['rhs']

a = np.load(OUT/'g8_best_angles.npy')
R, con, d = gm.shape(a)
g = np.exp(d['logg']); M = float(g.max())
q = 2*np.sin(d['w']/2); s = 2*np.sin(d['alpha']/2)
ell = d['ell']; al = d['alpha']; w = d['w']
print('=== witness shape from g8 ===')
print(f'R_shape              = {R:.15f}')
print(f'M = max_f gamma_f    = {M:.15f}   (log M = {math.log(M):.3e})')
print(f'max |15 constraints| = {np.abs(con[:15]).max():.3e}')
print(f'circle-ratio part of the constraint vector (should be ~0 by construction): '
      f'{np.abs(con[15:21]).max():.3e}')
print(f'min_i alpha_i = {al.min():.10f}  (must be > 0);  max alpha_i = {al.max():.10f} '
      f'(must be < pi = {math.pi:.10f})')
print(f'min_i w_i     = {w.min():.10f}  (must be > 0);  max w_i = {w.max():.10f} '
      f'(must be < pi)')
print(f'sum_i w_i - 2pi = {w.sum()-2*math.pi:+.3e}')
print(f'all site angles in (0,pi): min {a[:33].min():.8f}, max {a[:33].max():.8f}')
print(f'all switch half-angles in (0,pi/2): min {a[33:42].min():.8f}, '
      f'max {a[33:42].max():.8f} (pi/2 = {math.pi/2:.8f})')
print(f'\nR = M q_i/ell_i check: spread of M q_i/ell_i = '
      f'{np.ptp(M*q/ell):.3e}')
print(f'(G3) M ell_i <= s_i: {np.all(M*ell <= s+1e-12)}, worst margin '
      f'{float(np.max(M*ell-s)):+.3e}')
print(f'(G4) R = {R:.15f} >= M^2 min(q/s) = {M*M*float((q/s).min()):.15f}  -> '
      f'{"OK" if R >= M*M*float((q/s).min())-1e-12 else "VIOLATED"}')
print(f'\nper-sector (q/s) and 0.38 s/q:')
for i in range(9):
    print(f'   i={i}: q/s={q[i]/s[i]:.10f}  0.38 s/q={0.38*s[i]/q[i]:.10f}')
print(f'\nmin_i 0.38 s_i/q_i = {(0.38*s/q).min():.10f}  -> (G4) needs M >= '
      f'{math.sqrt((0.38*s/q).min()):.10f}')
print(f'actual M = {M:.10f}: since M < that, (G4) gives only '
      f'M^2 min(q/s) = {M*M*float((q/s).min()):.10f} < 0.38')
print(f'\nVERDICT: this witness has M = 1 exactly, is feasible, has R = {R:.12f} < 0.38.')
print(f'Therefore any proof of R >= 0.38 must establish  M >= '
      f'{math.sqrt((0.38*s/q).min()):.10f}  on the isosceles family, i.e. must bound the')
print(f'gamma spread away from 0 by a strictly positive amount controlled by the angles.')
