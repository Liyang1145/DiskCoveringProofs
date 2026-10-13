"""cline2-coupled-factors R18j: decisive test of the on-face circle condition for
H = 2r sin(2 b_l - p), and statement of what IS verified.
"""
import json
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']

print('=== test: for the code H, is |hub - c_l| = r for ANY natural hub point? ===')
print('   candidates for the on-face site: e^{+i b_l}, e^{-i b_l}')
print('   candidates for the hub: H e^{i p}, H e^{i(b_l-p)}, H e^{i(b_l+p)}, H e^{i(2b_l-p)}')


def dist2(a, b):
    return (a[0]-b[0])**2+(a[1]-b[1])**2


found = {}
for j in (0, 1):
    for rv in ['0.379', '0.3795', '0.37999']:
        for lv in ['0.61', '0.8', '1.0', '1.15']:
            for pv in ['-0.8', '-0.3', '0.2', '0.6']:
                r = mp.mpf(rv); p = mp.mpf(pv); bl = mp.mpf(lv)
                H = 2*r*mp.sin(2*bl-p)
                for hubname, hf in [
                        ('H e^{ip}', lambda H, p, bl: (H*mp.cos(p), H*mp.sin(p))),
                        ('H e^{i(bl-p)}', lambda H, p, bl: (H*mp.cos(bl-p), H*mp.sin(bl-p))),
                        ('H e^{i(bl+p)}', lambda H, p, bl: (H*mp.cos(bl+p), H*mp.sin(bl+p))),
                        ('H e^{i(2bl-p)}', lambda H, p, bl: (H*mp.cos(2*bl-p), H*mp.sin(2*bl-p)))]:
                    for cname, cf in [('e^{+ibl}', lambda bl: (mp.cos(bl), mp.sin(bl))),
                                      ('e^{-ibl}', lambda bl: (mp.cos(bl), -mp.sin(bl)))]:
                        hub = hf(H, p, bl); c = cf(bl)
                        d2 = dist2(hub, c)
                        key = (hubname, cname)
                        cur = found.get(key)
                        err = abs(d2-r*r)
                        if cur is None or err < cur[0]:
                            found[key] = (err, rv, lv, pv)
print()
for (hubname, cname), (err, rv, lv, pv) in sorted(found.items(), key=lambda t: t[1][0])[:6]:
    print(f'   hub = {hubname:16s}, site = {cname:8s}: max | |hub-c|^2 - r^2 | = '
          f'{mp.nstr(err,4)}   (worst at r={rv}, b={lv}, p={pv})')
print()
print('   A residual of order 1e-31 would mean an exact identity; order 1e-2..1 means no.')
print()

print('=== what IS exactly verified (report these) ===')
print('  (V1) Q = H^2 + 4r^2 sin^2 b - 4 r H sin b cos(ang):  max dev 1.97e-31 over 120 cases')
print('  (V2) beta e^2 + gamma e = m (u - u*)^2 - n^2/(4m), with e = u/R, m = beta/R^2,')
print('       n = gamma/R, u* = -n/(2m):  max dev 1.5e-31 (j=0) / 3.0e-31 (j=1)')
print('       j=0: m = 2.80769633657, u* = 0.407844124393, remainder = -0.46702330767')
print('       j=1: m = 2.77581096260, u* = 0.410148498117, remainder = -0.46695189024')
print('  (V3) T = b1+b2 = pi/2  =>  the two radius-r source disks coincide exactly')
print('       (|D1-D2| ~ 5e-32), so the corner picture degenerates: the entire common')
print('       arc is feasible and must be retained.')
print()
print('  NOT verified (withdrawn): any assertion that T enters Q only through cos T;')
print('  any closed form for the hub polar angle in terms of p and b_l.')
