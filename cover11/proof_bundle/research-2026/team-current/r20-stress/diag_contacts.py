"""Which geometric contacts are active at the TC root? |H_l-U_k|, |H_l-B_k|, |H_l-waist|, central."""
import os, sys
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp
W = Path(__file__).parent
sys.path.insert(0, str(W))
SRC = (W / 'phase5c_scale_audit.py').read_text(encoding='utf-8')
pre = SRC.split('# ---------------------------------------------------------------- high precision chart Jacobians')[0]
NS = {'__name__': '__main__', '__file__': str(W / 'phase5c_scale_audit.py')}
exec(compile(pre, str(W / 'phase5c_scale_audit.py'), 'exec'), NS)
u0, tc_geo, at, res5, faces = NS['u0'], NS['tc_geo'], NS['at'], NS['res5'], NS['faces']
mp = NS['mp']; mp.mp.dps = 60
g = tc_geo(u0)
R = g['R']
dist = lambda p, q: mp.sqrt((p[0]-q[0])**2 + (p[1]-q[1])**2)
print('R =', mp.nstr(R, 12))
print()
print('            |H0-U_k|-R      |H1-U_k|-R      |H0-B_k|-R      |H1-B_k|-R    |B_k-...|')
for k in range(9):
    row = [dist(g['U'][k], g['hubs'][0]) - R, dist(g['U'][k], g['hubs'][1]) - R,
           dist(g['Bp'][k], g['hubs'][0]) - R, dist(g['Bp'][k], g['hubs'][1]) - R]
    print('  k=%d   %+.3e   %+.3e   %+.3e   %+.3e' % (k, row[0], row[1], row[2], row[3]))
print()
print('central: |waist - C6| - R = %+.3e ; |waist - C2| - R = %+.3e ; |waist - hubs| - R = %+.3e, %+.3e'
      % (dist(g['waist'], g['C'][6]) - R, dist(g['waist'], g['C'][2]) - R,
         dist(g['waist'], g['hubs'][0]) - R, dist(g['waist'], g['hubs'][1]) - R))
print()
print('hub-to-boundary-junction (all k, both hubs): sorted by |.|-R')
vals = []
for k in range(9):
    for l in range(2):
        vals.append((float(abs(dist(g['Bp'][k], g['hubs'][l]) - R)), k, l, float(dist(g['Bp'][k], g['hubs'][l]) - R)))
vals.sort()
for v in vals[:6]:
    print('   |B_%d - H%d| - R = %+.6e' % (v[1], v[2], v[3]))
print()
print('hub norms and pairwise:  |H0| = %.6f |H1| = %.6f |H0-H1| = %.6f ; R = %.6f'
      % (abs(g['hubs'][0][0]), abs(g['hubs'][1][0]), abs(g['hubs'][0][0] - g['hubs'][1][0]), R))
print('central circle radius: waist to hubs = %.6f, %.6f (= R identically)' % (dist(g['waist'], g['hubs'][0]), dist(g['waist'], g['hubs'][1])))
print()
print('switch half-angles b (model angle 33..41, deg):', [mp.nstr(mp.degrees(at(u0)['b'][0] * 0 + NS['model_quant'](NS['angle_vector'](u0))['w'][0]), 6)])
Q = at(u0)
print('arc widths w_i (deg):', [round(float(mp.degrees(Q['w'][i])), 4) for i in range(9)], ' sum =', round(float(mp.degrees(sum(Q['w']))), 6))
print('sector apertures alpha_i (deg):', [round(float(mp.degrees(Q['al'][i])), 4) for i in range(9)])
print('b_i (deg):', [round(float(mp.degrees(mp.asin(min(1, mp.mpf(1)) * 0 + mp.sin(NS['angle_vector'](u0)[33 + i])))), 4) for i in range(9)])
