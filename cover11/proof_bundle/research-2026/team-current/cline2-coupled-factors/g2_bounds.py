"""cline2-coupled-factors g2: global lower-bound candidates for R_shape (no sampling).

The exact identity chain at any legal shape:
  (I1)  R_shape = M * q_0/ell_0 with M = max_f gamma_f and q_i = 2 sin(w_i/2).
  (I2)  the six circle equations force q_i/ell_i = q_0/ell_0 for i=1..6, so
            R_shape = M q_i/ell_i   for EVERY i in 0..8.
  (I3)  with 0 < M < 1 and the convention z_i = gamma_{11+i},
            M^2 ell_i^2 = z_{i-1}^2 + z_i^2 - 2 z_{i-1} z_i cos(alpha_i).
Three elementary global inequalities follow from (I2) alone (any weights l_i >= 0
summing to 1 is a valid averaging, since all nine ratios are equal):
  (A) arithmetic mean:    M q0/ell0 = (1/9) sum_i M q_i/ell_i >= (1/9) sum_i q_i / max_i ell_i
                          >= (1/9) * (2/pi)*sum_i w_i / max_i ell_i = (4/9)/max_i ell_i
                          using sum_i w_i = 2 pi and 2 sin(x/2) >= (2/pi) x on [0,pi].
  (B) weighted geometric: M q0/ell0 = prod_i (M q_i/ell_i)^{l_i}
                          >= [ prod_i q_i / prod_i ell_i ]  * M   (weights 1/9 each)
                          >= [ prod_i q_i ]^{1/9} / [prod_i ell_i]^{1/9} * M.
  (C) per-sector:        M q_i/ell_i >= M (2/pi) w_i / ell_i, so
                          M >= R_shape * ell_i*pi/(2 w_i) for every i.
This script computes all the quantities needed, evaluates the candidates, and reports the
shortfall.  No grids, no claims.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np, math, json
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
pi = math.pi

ns = {'__file__': str(LEAD/'q0_exact_closure_radius.py')}
exec((LEAD/'q0_exact_closure_radius.py').read_text().split('res=ceq(x0)')[0], ns)
import sys
sys.path.insert(0, str(P))
from g1_structure import shape, ns as ns1, A, B   # reuse the verified machinery
ns = ns1

a0 = ns['x0'][:42]
R, con, d = shape(a0)
M = float(np.exp(d['logg']).max())
ell = d['ell']; w = d['w']; al = d['alpha']; rat = d['rat']
z = np.exp(d['logg'])[11:]           # switch radii in the root gauge
gam = np.exp(d['logg'])
print(f'candidate: R_shape = {R:.16f}, M = {M:.12f}')
print(f'sum_i ell_i = {ell.sum():.12f}   (per-sector: {np.round(ell,6)})')
print(f'prod_i ell_i = {np.prod(ell):.10f}   (log = {np.log(ell).sum():.10f})')
print(f'sum_i w_i = {w.sum():.15f}  (2pi = {2*pi:.15f})')
print(f'prod_i 2 sin(w_i/2) = {np.prod(2*np.sin(w/2)):.10f}')
print(f'sum_i 2 sin(w_i/2) = {np.sum(2*np.sin(w/2)):.12f}   (4 = (2/pi)*2pi)')
print(f'max_i ell_i = {ell.max():.12f}   min_i ell_i = {ell.min():.12f}')
print(f'M^2 (exact from (I3), u=v=1 at candidate? switches: '
      f'{np.round(z/M, 10)})')

# ---- candidate (A) arithmetic mean route ----
A_bound = (4/9)/ell.max()
print(f'\n(A) arithmetic route: (4/9)/max ell = {A_bound:.12f}   '
      f'-> shortfall vs 0.38: {A_bound-0.38:+.6f}; vs R_cert: {A_bound-R:+.6f}')
# sharper: use the actual sum of 2 sin(w/2) with the constraint sum w = 2pi
sumq = float(np.sum(2*np.sin(w/2)))
A2 = (sumq/9)/ell.max()
print(f'(A2) using actual sum_i 2sin(w_i/2) = {sumq:.6f}: '
      f'(sumq/9)/max ell = {A2:.12f}')
# with the Taylor bound sum sin ~ sum w - sum w^3/24, maximize over w_i in [wmin,wmax]
# subject to sum w = 2pi: the concave objective is maximized at equal w's, giving the
# GLOBAL value below (valid for ALL legal shapes with w_i in [0,pi]):
wbar = 2*pi/9
sumq_max = 9*2*math.sin(wbar/2)
print(f'    global bound sum_i 2sin(w_i/2) <= {sumq_max:.10f} (attained at w_i = 2pi/9), '
      f'actual {sumq:.6f}')
A3 = (sumq/9)/ell.max()
print(f'(A3) with the global cap: sumq_max/(9 max ell) = {sumq_max/(9*ell.max()):.12f}')

# ---- candidate (B) weighted geometric route ----
B_bound = (np.prod(2*np.sin(w/2)))**(1/9)/ (np.prod(ell))**(1/9)
print(f'\n(B) geometric route: prod(q)^{1/9}/prod(ell)^{1/9} = {B_bound:.12f}')
print(f'    shortfall vs 0.38: {B_bound-0.38:+.6f}')

# ---- candidate (C) per-sector ----
C = [R*ell[i]*pi/(2*w[i]) for i in range(9)]
print(f'\n(C) per-sector implied M >= R ell_i pi/(2 w_i): max = {max(C):.12f} '
      f'(so M would need >= {max(C):.6f}; actual M = 1, so this gives R >= '
      f'{2*w[int(np.argmax(C))]/ell[int(np.argmax(C))]/pi:.6f})')

# ---- what the structure actually delivers: the exact switch identity ----
# 2 sin(b_i) = R * eta_i with eta_i = M ell_i / R_shape-consistent scaling; compute eta
eta = M*ell/R if False else None
# from (I2): 2 sin(b_i)/ell_i = M q_0/ell_0 / (z-pair factor) -> compute directly
ell_norm = np.sqrt((np.roll(z, 1)/M-np.roll(z, 1)/M)**2)  # placeholder
eta = M*ell
print(f'\neta_i = M ell_i = {np.round(eta, 8)}')
print(f'ratio eta_min/M = {ell.min():.8f}, eta_max/M = {ell.max():.8f}')
print(f'so the per-sector identity reads  2 sin(b_i) = R * eta_i / M; '
      f'equivalently R = 2 sin(b_i) M/(M ell_i) = 2 sin(b_i)/ell_i * M '
      f'(consistent with I1)')

# ---- sum of the nine switch chord identities: the global scaling relation ----
sinb = np.sin(np.array(ns['x0'][33:42]))
print(f'\nswitch half-angles b_i and sin(b_i):')
for i in range(9):
    print(f'   i={i}: b={ns["x0"][33+i]:.8f}  sin b={sinb[i]:.8f}  '
          f'2 sin b/ell={2*sinb[i]/ell[i]:.12f}')
print(f'2 sin(b_i)/ell_i should equal M q_0/ell_0 / (gamma-pair normalization) = '
      f'{np.round(2*sinb/ell, 12)}')
print(f'\nmax_i 2 sin(b_i) = {np.max(2*sinb):.8f};  sum_i 2 sin(b_i) = '
      f'{np.sum(2*sinb):.8f}')
print(f'bound on R from the largest switch: R = 2 sin(b_j) M/(M ell_j) <= '
      f'{np.max(2*sinb)/ (np.min(ell)):.10f} (trivial)')

# ---- KEY: what would make the bound work: the product/sum of the nine ell_i ----
print(f'\n--- requirement analysis ---')
print(f'To reach R >= 0.38 via (A) one needs max_i ell_i <= 4/(9*0.38) = '
      f'{4/(9*0.38):.6f}; actual max ell = {ell.max():.6f} '
      f'(ratio {ell.max()/(4/(9*0.38)):.4f})')
print(f'To reach R >= 0.38 via (B) one needs prod ell_i^{{1/9}} <= '
      f'{(np.prod(2*np.sin(w/2)))**(1/9)/0.38:.6f}; actual '
      f'{(np.prod(ell))**(1/9):.6f} (ratio {((np.prod(ell))**(1/9))/((np.prod(2*np.sin(w/2)))**(1/9)/0.38):.4f})')
print(f'So both elementary routes need an upper bound on ell_i.  ell_i is a distance '
      f'between the two switch points of sector i; its only global constraint is that all '
      f'nine switches lie on the unit circle, giving sum |P_{i+1}-P_i| <= 2pi.  The '
      f'perimeter bound is 2pi = {2*pi:.4f} while sum_i ell_i = {ell.sum():.4f}.')
