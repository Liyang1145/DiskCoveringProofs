"""R18: explicit numeric demonstration of the sign in the stationary Taylor correction.

Take any 1-D function with a stationary maximum and evaluate what lines 26-31 produce.
The question is only about direction: f(d*) vs f(mid) - (|h|/2)(d*-mid)^2.
"""
import math, sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

# a concrete 1-D analogue with the same signs: concave, stationary max at d*
f = lambda T: -0.5 * (T - 2.175) ** 2 + 10.0
fd = lambda T: -(T - 2.175)
fdd = lambda T: -1.0

mid = 2.20
dstar = 2.175                     # stationary point of the same function
h2 = 1.0                          # |f''| bound on the segment

val_mid = f(mid)
true_star = f(dstar)
centered = val_mid - 0.5 * h2 * (dstar - mid) ** 2

print('1-D analogue (concave, stationary max at 2.175):')
print(f'  f(mid)      = {val_mid:.9f}')
print(f'  f(d*)       = {true_star:.9f}')
print(f'  f(d*) - f(mid) = {true_star - val_mid:+.9f}   (>=0 : the stationary value is HIGHER)')
print(f'  code centered = f(mid) - h2/2 (d*-mid)^2 = {centered:.9f}')
print(f'  centered <= f(d*)? {centered <= true_star}   (if the code used centered as an UPPER')
print('   bound on f(d*) it would claim f(d*) <= centered, which is FALSE here)')
print()
print('  Conclusion: with f\'\' <= 0 (the case line 34 keeps), the code\'s centered value is a')
print('  LOWER bound on the stationary value, not an upper bound. Using it as an upper bound')
print('  understates the stationary value by 0.5|f\'\'|(d*-mid)^2.')

print()
print('exact algebra for the general case:')
print('   f(d*) = f(mid) + f\'(mid)(d*-mid) + 0.5 f\'\'(xi)(d*-mid)^2')
print('   stationarity of d* gives f\'(mid) = f\'\'(eta)(d*-mid), so')
print('   f(d*) = f(mid) + (d*-mid)^2 [ f\'\'(eta) + 0.5 f\'\'(xi) ]')
print('   with f\'\' <= 0 throughout: f(d*) <= f(mid)  and the correction term is NEGATIVE,')
print('   i.e.  f(d*) = f(mid) - (1/2)|f\'\'| (d*-mid)^2 + O(...), which is ABOVE centered.')
print()
print('note: line 26 (a.d = am.d + am.h*(x-mid)) is a sound first-order enclosure of the')
print('derivative column; the problem is only line 29 used as a value bound.')

print()
print('=' * 72)
print('does the correction actually bind? inspect the saved boxes')
print('=' * 72)
import json
from pathlib import Path
L = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
d = json.loads((L / 'stationary_face_bound_probe.json').read_text())
print('probe keys:', list(d.keys()))
print('count', d.get('count'), 'live', d.get('live'), 'terminal', d.get('terminal'))
print('closed', d.get('closed'))
tb = d.get('topboxes', [])
print(f'topboxes stored: {len(tb)}')
for r in tb[:3]:
    print('  j=', r['j'], 'box=', [[round(x, 5) for x in p] for p in r['box']], 'upper=', r['upper'])
