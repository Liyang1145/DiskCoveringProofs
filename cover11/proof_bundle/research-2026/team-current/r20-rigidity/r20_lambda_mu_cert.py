"""r20-rigidity: CONDITIONAL bound candidates for lambda and mu (NOT certificates).

RETRACTION (lead audit, 2026-09-25): the earlier version announced "certified coarse lambda/mu" and a
"true certificate".  Withdrawn:
  * the 2x2 Schur/trace ratio is not a valid eigenvalue lower bound in general -> replaced by the
    safe pencil bound  det(B)_lower / ( tr(B)_upper * tr(G)_upper )   [valid when B is PD:
    lambda_min(B,G) >= det(B)/(tr(B) tr(G)) ],
  * sigma17, the symmetric metric factor (1/3) and the L2/L3 coefficients are numeric/unchecked,
  * hence nothing here is certified and no claim is added to the registry.
Status: conditional bound candidates; the analytic mu / minor-bound interface is being provided by the
chain and is to be substituted here.

Writes r20_lambda_mu_cert.json / .log.
"""
import json
from pathlib import Path
import mpmath as mp

P = Path(__file__).parent
mp.mp.dps = 40
REP = []


def say(s):
    print(s, flush=True)
    REP.append(s)


say('[R0] RETRACTED: earlier "certified coarse lambda/mu" wording (lead audit). '
    'This run reports conditional candidates only.')

# ---- (1) anti quotient: safe 2x2 pencil bound on the C901 interval data
detB = mp.mpf('0.21779896923847451425')                     # C901 det_interval lower endpoint
trB = mp.mpf('13.1533') + mp.mpf('4.2819')                  # B2 diagonal upper endpoints (conservative)
trG = mp.mpf('53.25') + mp.mpf('20.34')                     # G2 diagonal upper endpoints (conservative)
lam_anti_cand = detB / (trB * trG)
say('[L1] safe 2x2 pencil candidate: det(B)_lo/(tr(B)_hi tr(G)_hi) = %s/(%s * %s) = %.6f'
    % (mp.nstr(detB, 18), trB, trG, lam_anti_cand))
say('     (needs B PD as an input: C901 records det(B) > 0 and B11 > 0; B22 not recorded yet)')

# ---- (2) symmetric side candidate (lead C893 plus a numeric metric factor)
lam_sym_cand = mp.mpf(1) / 4 * mp.mpf(1) / 3
say('[L2] sym side candidate: (1/4)*(1/3) = %.6f ; the factor 1/3 is NUMERIC (recorded chart metric '
    '0.3519) -> conditional' % lam_sym_cand)
lam_cand = min(lam_anti_cand, lam_sym_cand)
say('[L3] conditional lambda candidate = %.6f (numeric point value 0.164903)' % lam_cand)

# ---- (3) mu candidate (formula level, numeric sigma17)
w_min = mp.mpf('0.0098946876')
mu_cand = w_min * mp.mpf('0.0584199083') / mp.sqrt(18)
say('[M1] mu candidate: w_min * sigma17 / sqrt(18) = %.6e ; sigma17 NUMERIC -> conditional'
    % mu_cand)

# ---- (4) box with the crude (unchecked) L2/L3
L2 = mp.mpf('19345360.1411')
L3 = mp.mpf('139542042902.4849')
M = L2
eta = min(mp.mpf(1) / 4, lam_cand / (16 * M))
rho = min(mp.mpf(1), mu_cand * eta / L2, lam_cand / (2 * L3))
c = min(mu_cand * eta / (2 * rho), lam_cand / 4)
say('[B1] conditional eta = %.3e ; rho = %.3e ; c = %.3e (upstream inputs numeric/unchecked)'
    % (eta, rho, c))

OUT = {'status': 'RETRACTED wording; conditional candidates only; nothing certified; no claim added',
       'lambda_anti_candidate': mp.nstr(lam_anti_cand, 20),
       'lambda_sym_candidate': mp.nstr(lam_sym_cand, 20),
       'lambda_candidate': mp.nstr(lam_cand, 20), 'mu_candidate': mp.nstr(mu_cand, 20),
       'eta_candidate': mp.nstr(eta, 12), 'rho_candidate': mp.nstr(rho, 12), 'c_candidate': mp.nstr(c, 12),
       'unchecked_inputs': ['sigma17 (numeric 0.0584199083)', 'sym metric factor 1/3 (numeric 0.3519)',
                            'L2/L3 coefficients (no symbolic check)', 'B2 PD (B22 unrecorded)'],
       'repro': 'py -3 -B -X utf8 r20_lambda_mu_cert.py'}
(P / 'r20_lambda_mu_cert.json').write_text(json.dumps(OUT, indent=2))
(P / 'r20_lambda_mu_cert.log').write_text('\n'.join(REP) + '\n')
say('\nwritten r20_lambda_mu_cert.json / .log')
