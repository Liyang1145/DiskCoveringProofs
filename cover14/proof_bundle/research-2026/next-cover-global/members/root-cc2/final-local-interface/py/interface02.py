"""root-cc2 final-local-interface: re-verify the (ENTRY) ratio with the SAVED beta.

Trace of the discrepancy: diagnostic.py line 62 uses beta = anchor_eps + alpha (the
POST-GAUGE anchor bound), not anchor_eps.  Using beta = 2e-6 gives a different ratio.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp

ROOT = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global')
HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)
log = []
def L(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

d = json.loads((ROOT / 'members/q10-effective-localization/diagnostic.json').read_text())
E = d['exact']
b = F(E['b']); B = F(E['W_norm_squared_upper']); mu = F(E['mu']); kap = F(E['kappa'])
eta = F(E['U_minus_rstar_upper'])
h0 = F(E['h0']); a_rep = F(E['repair_coefficient'])
A2 = d['anchor_only_2e6']
anchor_eps = F(A2['epsilon']); alpha = F(A2['gauge_angle_upper']); beta_saved = F(A2['post_gauge_anchor_bound'])
exit_rhs_saved = F(A2['exit_rhs']); exit_lhs_saved = F(A2['exit_lhs'])

L('=' * 78)
L('(1) the exact tokens from diagnostic.py')
L('  eta  (U_minus_rstar_upper) = %s' % eta)
L('  h0   = %s ; repair_coefficient a = %s' % (h0, a_rep))
L('  kappa = %s' % kap)
L('  eps   = 1/25000')
L('  anchor_eps = %s ; gauge_angle_upper alpha = %s' % (anchor_eps, alpha))
L('  beta (post_gauge_anchor_bound) = %s' % beta_saved)
L('  line64: exit_rhs = (665/1000)*(eta + a*beta^2)')
L('  line65: exit_lhs = kappa*eps^2')
L('')

L('=' * 78)
L('(2) recomputation with the SAVED beta (line 62 value)')
e2 = F(1, 25000) ** 2
rhs = F(665, 1000) * (eta + a_rep * beta_saved * beta_saved)
lhs = kap * e2
L('  RHS = %s' % rhs)
L('  LHS = %s' % lhs)
L('  RHS/LHS = %.17g' % float(rhs / lhs))
L('  saved exit_rhs  = %s  (match: %s)' % (exit_rhs_saved, rhs == exit_rhs_saved))
L('  saved exit_lhs  = %s  (match: %s)' % (exit_lhs_saved, lhs == exit_lhs_saved))
L('  saved display_ratio = %.17g' % A2['display_ratio'])
L('  => the saved numbers are exactly this formula; RHS<LHS: %s' % (rhs < lhs))

L('')
L('=' * 78)
L('(3) the source of my earlier 0.199: I used beta = anchor_eps instead of the post-gauge beta')
rhs_wrong = F(665, 1000) * (eta + a_rep * anchor_eps * anchor_eps)
L('  with beta=anchor_eps=%s: RHS/LHS = %.10f  (what I reported)' % (anchor_eps, float(rhs_wrong / lhs)))
L('  with beta=post_gauge=%s: RHS/LHS = %.10f  (saved)' % (beta_saved, float(rhs / lhs)))
L('  ratio of the two betas^2 = %.6f' % float((beta_saved * beta_saved) / (anchor_eps * anchor_eps)))
L('  => confirmed arithmetic slip on my side (beta token), NOT a bookkeeping difference.')

L('')
L('=' * 78)
L('(4) containment direction, restated correctly')
L('  for a vector v in R^28 at the SAME epsilon: |v|_inf <= |v|_2, so')
L('      { |v|_2 <= eps } subset { |v|_inf <= eps }.')
L('  The Euclidean ball is the SMALLER set: the sup-norm box is WEAKER (a larger region).')
L('  A positive-definiteness statement on the sup box is therefore a statement on the')
L('  smaller Euclidean ball as well; it is the sup box that is the weaker hypothesis.')
L('  (My earlier wording "stronger than what is needed" reversed this.)')

L('')
L('=' * 78)
L('(5) K = 29/9')
L('  K = %s appears only in the SEPARATE optional joint-gauge (Procrustes) variant,'
  % F(E['K']))
L('  where the final X+ alignment inflates per-site error by at most K. It is NOT the')
L('  anchor-lens factor; the lens factor is alpha = H/[2 r* (s - sqrt H)] (%s).' % alpha)

(OUT / 'interface02.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'interface02.txt')
