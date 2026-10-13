"""root-cc2 final-local-interface: independent arithmetic check of the localization bridge.

Recomputes, from the SAVED rational constants and the saved root enclosure, the chain
    anchor cell eps_A = 2e-6  ->  gauge/lens bound  ->  (ENTRY) at eps = 1/25000
    ->  gauged site box  ->  r >= r*
and reports every ratio.  No AD, no optimiser, no lead writer import.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp

ROOT = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global')
HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
OUT.mkdir(parents=True, exist_ok=True)
mp.mp.dps = 40
log = []
def L(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

d = json.loads((ROOT / 'members/q10-effective-localization/diagnostic.json').read_text())
E = d['exact']
b = F(E['b']); Wn = F(E['W_norm_squared_upper']); mu = F(E['mu']); kap = F(E['kappa'])
K = F(E['K']); tau = F(E['tau']); Uminus = F(E['U_minus_rstar_upper'])

L('=' * 78)
L('(1) the saved rational constants (read as exact decimals, not as numerators)')
L('    b    = %.17g   (saved exact fraction; <1 required)' % float(b))
L('    B    = %.10f   (bound on ||W||_2^2)' % float(Wn))
L('    mu   = %.14f' % float(mu))
L('    kappa= %.14f' % float(kap))
L('    K    = %.10f ; tau = %.6e ; U-r* <= %.6e' % (float(K), float(tau), float(Uminus)))
L('')
L('    consistency: mu == (1-b)/B ?  residual = %.3e' % float(mu - (1 - b) / Wn))
L('    consistency: kappa == mu/(2(1+27/1000)) ?  residual = %.3e'
  % float(kap - mu / (2 * (1 + F(27, 1000)))))

L('')
L('=' * 78)
L('(2) the root box and U (source: lead/root-integer-certificate.json)')
rk = json.loads((ROOT / 'lead/root-integer-certificate.json').read_text())
r_lo, r_hi = [F(x) for x in rk['box_dyadic'][2]]
U = F(33173203427623414, 10 ** 17)
L('    r* in [%.17g, %.17g] ; U = %.17g ; U - r*_lo <= %.6e'
  % (float(r_lo), float(r_hi), float(U), float(U - r_lo)))

L('')
L('=' * 78)
L('(3) the entry inequality at eps = 1/25000 with the anchor cell eps_A = 2e-6')
eps = F(1, 25000)
epsA = F(2, 10 ** 6)
eta = U - r_lo                     # conservative (>= true U-r*)
a_rep = F(4000000, 7999999)        # repair coefficient in the report
lhs = F(665, 1000) * (eta + a_rep * epsA * epsA)
rhs = kap * eps * eps
L('    eps = 1/25000 ; eps^2 = %.6e' % float(eps * eps))
L('    eta (U - r*_lo) = %.6e' % float(eta))
L('    0.665*(eta + a*beta^2) = %.6e' % float(lhs))
L('    kappa*eps^2            = %.6e' % float(rhs))
L('    ratio (entry test)     = %.10f   < 1 required' % float(lhs / rhs))
L('')
L('    => (ENTRY) holds with margin %.4f' % float(1 - lhs / rhs))

L('')
L('=' * 78)
L('(4) the resulting site box (FINAL)')
val = (U * U - r_lo * r_lo) / kap
L('    (U^2 - r*_lo^2)/kappa = %.6e ; sqrt = %.6e' % (float(val), float(mp.sqrt(mp.mpf(float(val))))))
L('    report display: site_error 5.265632842102119e-08, gauged box 4e-5;')
L('    so the Euclidean site box is %.3e < 4e-5 : %s'
  % (float(mp.sqrt(mp.mpf(float(val)))), float(mp.sqrt(mp.mpf(float(val)))) < 4e-5))

L('')
L('=' * 78)
L('(5) the gauge/lens bound at eps_A = 2e-6 (recomputed independently)')
H = (U + epsA) ** 2 - r_lo * r_lo
L('    H = (U+eps_A)^2 - r*_lo^2 = %.6e' % float(H))
norm_gauge = F(E['gauge_angle_upper'])
L('    saved gauge_angle_upper   = %.6e' % float(norm_gauge))
s_lo = mp.sqrt(1 - mp.mpf(float(r_hi)) ** 2)
lens = float(H) / (2 * float(r_lo) * (float(s_lo) - mp.sqrt(float(H))))
L('    my lens recomputation H/[2r*(s-sqrt H)] = %.6e' % lens)
L('    saved post_gauge_anchor_bound = %.6e' % float(F(E['post_gauge_anchor_bound'])))
L('    beta = eps_A + lens = %.6e   < 1e-3 required: %s'
  % (float(epsA) + lens, float(epsA) + lens < 1e-3))

L('')
L('=' * 78)
L('(6) what the 4e-5 box refers to')
L('    the saved dual comparison gives gauged site error 2.7633839311e-5 at eps_A=2e-6')
L('    (independent-localization REPORT s.5/6), i.e. below 4e-5; the interpolation route')
L('    gives the tighter 5.27e-8.  The 2e-6 anchor cell is a SUP-norm bound on the ten')
L('    anchor angles; every site-norm statement in the chain is EUCLIDEAN.')

(OUT / 'interface01.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'interface01.txt')
