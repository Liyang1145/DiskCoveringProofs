import json, os
from fractions import Fraction as F

base = r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\solo-20260922'
load = lambda f: json.load(open(os.path.join(base, f)))

print("=== exact rational check of the e-bound ===")
a = F(3*19, 50) - 1
print("  3R-1 = 3*(19/50)-1 =", a, "   7/50 =", F(7, 50), "   196/625 =", F(196, 625))
print("  3R-1 == 7/50 :", a == F(7, 50), "   7/50 == 196/625 :", F(7, 50) == F(196, 625))

print()
print("=== exact endpoints of the certified e-intervals ===")
for f in ['directional_low_cover.json', 'directional_e_cover.json']:
    rows = sorted(load(f)['runs'], key=lambda r: F(r['e_interval'][0]))
    print(' ', f)
    print('    first:', rows[0]['e_interval'], '  last:', rows[-1]['e_interval'])
    print('    last interval equals 7/50 exactly:', F(rows[-1]['e_interval'][1]) == F(7, 50))
print()
A = load('directional_low_cover.json')['runs'] + load('directional_e_cover.json')['runs']
print("  kernel A low-range file holds", len(load('directional_low_cover.json')['runs']), "runs:",
      [r['e_interval'] for r in load('directional_low_cover.json')['runs']])
print("  kernel A main file holds", len(load('directional_e_cover.json')['runs']), "runs")
print()
print("=== e-max bound used in the hub-cell step (B(0,a) subset V1) ===")
a = F(19,50)
print("  a = 1-2R = 1-38/50 =", 1 - 2*a, "   3R-1 =", 3*a - 1, "   equal:", (1-2*a) < (3*a-1))
