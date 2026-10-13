"""UNAMBIGUOUS direction test. Print the raw per-component angles and their sum
at y=1 for several x, plus the branch bound pi-beta. No case logic at all."""
import numpy as np
PI = np.pi
cases = {'1.2^3': [1.2, 1.2, 1.2], 'pi/2^3': [PI / 2] * 3, 'pi/4^3': [PI / 4] * 3,
         'cand': [0.9223829833, 1.1925065472, 1.1925065472], '1.0^3': [1.0] * 3}
for name, b in cases.items():
    b = np.array(b)
    print('===', name, 'beta=', np.round(b, 4), 'Bsum=%.5f' % b.sum())
    print('   pi-beta =', np.round(PI - b, 4), ' H(1) via (3pi-Bsum)/2 = %.6f'
          % ((3 * PI - b.sum()) / 2))
    for x in [0.05, 0.2, 0.4, 0.6, 0.8, 0.9, 0.95, 1.0]:
        th = np.arctan2(np.sin(b), x - np.cos(b))
        S = float(th.sum())
        branch = bool(np.all(th < PI - b))
        print('   x=%.2f theta=%s S=%.6f  S-pi=%+.6f  branch_ok=%s'
              % (x, np.round(th, 4), S, S - PI, branch))
