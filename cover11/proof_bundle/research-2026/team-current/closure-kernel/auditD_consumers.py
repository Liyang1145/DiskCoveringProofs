"""Audit D: remaining red-team points.
 (i)  where the certified 'growth' constant appears and whether anything downstream consumes it;
 (ii) the exact form of the code's stopping rule vs the doc's sufficient-radius inequality;
 (iii) the eps <= .001/nmax chain and the second rational assertion;
 (iv) the neumann refinement iteration count needed for the claimed radius.
"""
import json, re, sys
from fractions import Fraction as F
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
base = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current')
L = base / 'lead'

print('=== (i) consumers of the growth / certified constants ===')
hits = []
for p in base.rglob('*.py'):
    try:
        t = p.read_text(encoding='utf-8', errors='replace')
    except Exception:
        continue
    if 'growth' in t or 'certified_rational_constants' in t:
        for i, l in enumerate(t.splitlines(), 1):
            if 'growth' in l or 'certified_rational_constants' in l:
                hits.append((str(p.relative_to(base)), i, l.strip()[:150]))
for h in hits[:40]:
    print('  ', h[0], 'line', h[1], '|', h[2])
print(f'  total hits: {len(hits)}')

print()
print('=== (ii) stopping rule vs doc ===')
mu = F(1, 600); M = F(16000)
doc = lambda r: (2 * M + F(1, 2)) * r + (mu / 2 + 1) * M ** 2 * r ** 2
print('  code line 114:  while hi((2*M + .5)*rho + (mu/2 + 1)*M^2 rho^2) > mu/4:  rho /= 10')
print('  doc  line 24 :  (2M + 1/2)rho + (mu/2 + 1)M^2 rho^2 <= mu/4')
print(f'  the two are the SAME inequality; code starts at rho=0.01 and divides by 10')
for k in range(4, 11):
    r = F(1, 10 ** k)
    print(f'    rho = 1e-{k:<2d}: value = {float(doc(r)):.6e}  <= mu/4 = {float(mu/4):.6e} : '
          f'{doc(r) <= mu/4}')
print(f'  => largest power of ten passing is rho = 1e-8, matching rho_power10 = 1e-8 in the JSON')

print()
print('=== (iii) eps chain and the second rational assertion ===')
print('  code line 108: eps = lo(.001/nmax)   with nmax = max|N_ij|')
print('  code line 115: assert hi(eps*nmax) < .0029')
print('  N has 4 columns equal to the free basis vectors (unit entries), so nmax >= 1 and')
print('  eps <= .001/nmax, hence eps*nmax <= .001 < .0029 : the assertion is structural, not numeric.')
print(f'  => 0.001 < 0.0029 : {F(1,1000) < F(29,10000)}')

print()
print('=== (iv) how many Neumann iterations are actually needed ===')
for qv in (0.0002, 0.001263):
    print(f'  q = {qv:.6f}: q^k <= 0.01 needs k >= {__import__("math").ceil(__import__("math").log(0.01)/__import__("math").log(qv))}'
          f'  (code runs 12)')

print()
print('=== (v) the JSON contractions, as written by the script ===')
d = json.loads((L / 'interval_network_envelope.json').read_text())
print('  contractions [q(M), qB, qG, qL] =', d['contractions_diagnostic'])
print('  qGram =', d['quantitative_local_patch']['qGram'])
print('  lower > .95 :', d['preconditioned_HK_Gershgorin_gt_.95'],
      ' value', d['preconditioned_HK_lower_diagnostic'][:24])
print('  alpha_min > .0029 :', d['alpha_min_gt_.0029'],
      ' value', d['alpha_min_lower_diagnostic'][:24])
