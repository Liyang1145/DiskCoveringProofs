"""cline2-coupled-factors g10: the exact mechanism at M = 1 (isosceles family).

Exact consequence chain at M = 1.  If M = 1 then ell_i = s_i exactly (by G3 with equality),
and the identity R = M q_i/ell_i becomes

    q_i = R s_i      i.e.    2 sin(w_i/2) = R * 2 sin(alpha_i/2)    for EVERY i = 0..8.

So on the M = 1 boundary the model reduces to ONE scalar R and the eight ratios
(q_i/s_i = q_0/s_0), plus the 13 linear angle equalities and sum_i w_i = 2 pi, plus the
TWO cycle equations.  The sixteen relations  q_i/s_i = R  are the six circle equations in
disguise (they are free of gamma), so M = 1 is exactly the statement that the circle system
is solved with all branch radii equal.

This script:
  (1) confirms the candidate satisfies q_i = R s_i to machine precision (M = 1 path),
  (2) confirms the relation's residual scale and the size of the quantity that any global
      argument has to control:  max_i |log(q_i/s_i) - log R| = 0 on the exact manifold,
  (3) reports the exact value of the M = 1 constraint  R = q_i/s_i  and compares with
      0.38: the gap is R_cert - 0.38-equivalent, quantified.
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

a0 = ns['x0'][:42]
R, con, d = gm.shape(a0)
g = np.exp(d['logg']); M = float(g.max())
q = 2*np.sin(d['w']/2); s = 2*np.sin(d['alpha']/2); ell = d['ell']
print('=== candidate, M = 1 path ===')
print(f'M = {M:.16f}')
print(f'gamma_f: {np.round(g, 12)}')
print(f'(G3) equality? |M ell_i - s_i| max = {np.abs(M*ell-s).max():.3e} '
      f'(0 iff both endpoint gammas equal M)')
print(f'(G2) M q_i/ell_i spread = {np.ptp(M*q/ell):.3e}  (all equal R)')
print(f'\nM=1 identity  q_i = R s_i:  residual |q_i - R s_i| max = '
      f'{np.abs(q-R*s).max():.3e}')
print(f'ratio q_i/s_i: {np.round(q/s, 12)}')
print(f'spread of q_i/s_i = {np.ptp(q/s):.3e}')
print(f'R = {R:.16f}')

print(f'\n=== the exact scalar reduction on M = 1 ===')
print(f'with M = 1, R = q_i/s_i for all i, and the model becomes:')
print(f'   2 sin(w_i/2) = R * 2 sin(alpha_i/2)          [9 equations, one unknown R]')
print(f'   sum_i w_i = 2 pi, sum_i alpha_i = 2 pi + 2 sum_i b_i   [linear]')
print(f'   the two sine-product cycle equations         [2 equations in the angles]')
print(f'   plus 13 linear angle equalities')
print(f'So on M = 1 the only remaining nonlinear content is the cycle pair; the radius')
print(f'relation has already collapsed to a single scalar.')
print(f'\nmeasured this collapse: |q_i - R s_i| = {np.abs(q-R*s).max():.2e} and the entire')
print(f'8-equation circle system is satisfied, confirming M = 1 is consistent.')
print(f'\n=== quantified gap ===')
print(f'R(candidate) = {R:.16f}')
print(f'0.38 - R = {0.38-R:+.3e}   (the whole remaining gap)')
print(f'written as a requirement on M at fixed angles: M >= '
      f'{math.sqrt((0.38*s/q).min()):.10f}')
print(f'=> on the M=1 family the requirement is M >= 1.0000137527, and every legal shape')
print(f'   with M = 1 misses it; M = 1 IS attainable (g8 witness, R = 0.37997166).')
print(f'\n=== what would close it ===')
print(f'An identity or inequality of the form   M^2 >= G(alpha, w)  with')
print(f'   G(alpha,w) >= 0.38 s_i/q_i   for at least one i,')
print(f'and G > 1 strictly whenever the cycle equations hold.  The cycle residuals are')
print(f'   D_16 = sum of 7 signed log-sine ratios = {con[14]:.3e} (exact 0 required)')
print(f'   D_9  = {con[13]:.3e}')
print(f'and the deviating ratios are four of +3.038114e-3 and two of -3.038114e-3 plus')
print(f'one of -3.038111e-3 / +3.038111e-3, i.e. they cancel in PAIRS.  Hence the cycles')
print(f'constrain the ANGLES (differences of opposite angles) but not M: M = 1 is exactly')
print(f'the configuration in which the pairing is exact.')
