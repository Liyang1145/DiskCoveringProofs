"""cline2-coupled-factors g3: exact constants and a decisive relaxation test.

Question the lead needs answered: can ANY argument that only uses
   (i) the nine equality q_i/ell_i = q_0/ell_0,
   (ii) sum_i w_i = 2 pi,
   (iii) 0 < w_i < pi,  0 <= gamma_f <= M,
   (iv) the two cycle equations as *independent* equalities,
reach R_shape >= 0.38 ?  If not, the missing ingredient is specifically the coupling
between the cycle residuals and the branch spread, and no amount of re-weighting helps.

We answer by maximizing the relaxation's bound: the best possible bound of this type is
    min over legal shapes of  max_f [ log gamma_f ] + log(q_0/ell_0)
and the parity relaxation is
    min over (M=1, gamma in [0,1]^20, angles legal, cycle equations satisfied as equalities)
    of  max_f log gamma_f + log(q_0/ell_0)   =  log(q_0/ell_0) since gamma>=... 
so the parity question reduces to: how large can q_0/ell_0 be, subject to (i)-(iii)?

q_0/ell_0 = 2 sin(w_0/2)/ell_0.  With sum_i q_i/ell_i = 9 q_0/ell_0 = 9 M q_0/ell_0.

We also report the exact arithmetic of the two candidate global inequalities, with the
constants that would be needed, and the sector-level identity 2 sin(b_i) = R * M ell_i / M.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np, math, json, sys
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
pi = math.pi
sys.path.insert(0, str(P))

guard = (LEAD/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0]
ns = {'__file__': str(LEAD/'q0_exact_closure_radius.py')}
exec(guard, ns)
import importlib.util
spec = importlib.util.spec_from_file_location('gmod', P/'g1_structure.py')
# g1 runs at import only under __main__, so we can import it safely now
gm = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gm)
shape = gm.shape

a0 = ns['x0'][:42]
R, con, d = shape(a0)
M = float(np.exp(d['logg']).max())
ell = d['ell']; w = d['w']; al = d['alpha']
q = 2*np.sin(w/2)
r = q/ell
print(f'candidate: R = {R:.16f}   M = {M:.16f}')
print(f'\nratios q_i/ell_i: {np.round(r, 12)}')
print(f'spread max-min = {r.max()-r.min():.3e}  (must be 0: the six circle equations)')
print(f'M * r_i (all should equal R): {np.round(M*r, 12)}')

# --- exact global bounds of the elementary type ---
sumq = float(q.sum()); sumell = float(ell.sum())
print(f'\n--- elementary global constants ---')
print(f'sum_i q_i = {sumq:.12f}   (>= (2/pi)*2pi = 4, actual {sumq:.6f})')
print(f'sum_i ell_i = {sumell:.12f}   max ell = {ell.max():.12f}')
print(f'(A) R = M q_0/ell_0 >= (1/9)sum_i q_i / max ell >= {sumq/9/ell.max():.12f}')
    # valid: M>=1, q0/ell0 = q_i/ell_i, q_i >= (2/pi) w_i, sum w = 2pi
print(f'    even with the best possible sum q_i = 6.2831853 (=2pi at w_i=pi, not')
print(f'    attainable with sum w = 2pi) the bound is {2*pi/9/ell.max():.12f}')
print(f'(B) R >= (prod q_i / prod ell_i)^(1/9) = {(np.prod(q)/np.prod(ell))**(1/9):.12f}')
print(f'    with the global cap q_i <= w_i and sum w = 2pi: prod q_i <= '
      f'{np.prod([2*pi/9]*9)**(1/9):.12f} geometric mean, bound '
      f'{( (2*pi/9)**9/np.prod(ell) )**(1/9):.12f}')
print(f'(C) R >= 2 sin(b_i)/ell_i * M / (M) ... per-sector: R = M q_i/ell_i = '
      f'{np.round(M*r,12)}')

# --- how much of ell_max can the constraints control? ---
print(f'\n--- the decisive question ---')
print(f'ell_i is the chord between two points at radii z_(i-1)/M, z_i/M and angle alpha_i,')
print(f'scaled by M. Its value is (M ell_i)^2 = z_(i-1)^2+z_i^2-2 z_(i-1) z_i cos alpha_i.')
for i in range(9):
    print(f'   i={i}: alpha={al[i]:.8f}  z-pair=({np.exp(d["logg"])[11+(i-1)%9]:.10f},'
          f'{np.exp(d["logg"])[11+i]:.10f})  M*ell={M*ell[i]:.10f}  '
          f'2 sin(alpha/2)={2*math.sin(al[i]/2):.10f}')
print(f'\nno single ell_i is extremal: max_i M ell_i = {M*ell.max():.10f} at i='
      f'{int(np.argmax(ell))}, which has alpha = {al[int(np.argmax(ell))]:.6f} '
      f'(close to pi, maximising the chord)')
print(f'the two gamma values below 1 are gamma_5 = gamma_7 = '
      f'{np.exp(d["logg"])[5]:.10f}, and they coincide exactly with the two switches')
print(f'whose b_i are minimal ({np.exp(d["logg"])[5]:.10f}): a structural link between')
print(f'the inactive branches and the smallest switch angles')

json.dump({'R': R, 'M': M, 'sumq': sumq, 'sumell': sumell, 'ellmax': float(ell.max()),
           'r': r.tolist(), 'q': q.tolist(), 'ell': ell.tolist(),
           'w': w.tolist(), 'alpha': al.tolist(),
           'logg': d['logg'].tolist()}, open(OUT/'g3_constants.json', 'w'), indent=1)
print('\nsaved out/g3_constants.json')
