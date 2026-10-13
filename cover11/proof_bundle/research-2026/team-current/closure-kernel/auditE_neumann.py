"""Audit E: bound the Neumann-refinement truncation error and check it never matters."""
import sys
from fractions import Fraction as F
from pathlib import Path
import json, mpmath as mp

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
L = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
d = json.loads((L / 'interval_network_envelope.json').read_text())
q = [mp.mpf(x) for x in d['contractions_diagnostic']]
print('contractions:', [mp.nstr(x, 6) for x in q])
print()
print('the refinement is corr <- v + E*corr run 12 times, starting from corr_0 = [-eps,eps].')
print('truncation error after K steps <= eps * q^K/(1-q):')
for qi in q:
    for K in (2, 5, 12):
        err = mp.mpf(1) / 1000 * qi ** K / (1 - qi)
        print(f'  q={mp.nstr(qi,5)} K={K:2d}: eps*q^K/(1-q) = {mp.nstr(err, 8)}')
    print()
print('the enclosure only needs eps*q^K/(1-q) <= eps (i.e. q^K <= 1-q), which holds for q<1/2 and')
print('any K>=1. It is therefore impossible for the 12 iterations to be insufficient: the fixed')
print('point refinement is a contraction and the initial enclosure already covers the solution.')
print()
print('worst required K for q^K <= 1-q  at the largest observed q = 0.0012632:')
import math
qq = 0.001263177512518322
print(f'  K = {math.ceil(math.log(1-qq)/math.log(qq))} (code uses 12)')
