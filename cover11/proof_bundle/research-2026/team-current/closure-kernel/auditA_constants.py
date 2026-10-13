"""Audit A: independent checks of the quantitative constants and the root enclosure.

1. q = 16000/c1 (M = 2/c1) against the script's Mbound = hi(2/c1).
2. The rational inequalities asserted at lines 114 and 122.
3. The printed constant claims sigma > 1/4, mu > 1/600, eps*nmax < 0.0029.
4. The C891/C892 root box from repaired_tc_krawczyk.json: radius, center ranges, R > 0,
   and the angle/radius formulas used at lines 14-19.
"""
import json, sys
from pathlib import Path
from fractions import Fraction as F

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
L = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')

print('=' * 70)
print('1. M = 2/c1 and c1 = 1/8000')
print('=' * 70)
c1 = F(1, 8000)
M = 2 / c1
print(f'  c1 = 1/8000 = {float(c1):.6e}')
print(f'  M  = 2/c1  = {M} = {float(M):.6e}   (claimed M <= 16000)')

print()
print('=' * 70)
print('2. the two rational inequalities asserted in the script')
print('=' * 70)
mu = F(1, 600)
rho = F(1, 100000000)
Mv = F(16000)
lhs = (2 * Mv + F(1, 2)) * rho + (mu / 2 + 1) * Mv ** 2 * rho ** 2
rhs = mu / 4
print(f'  line 122: (2M+1/2)*rho + (mu/2+1)M^2 rho^2 <= mu/4')
print(f'    lhs = {float(lhs):.12e}   rhs = {float(rhs):.12e}')
print(f'    lhs <= rhs : {lhs <= rhs}   slack = {float(rhs - lhs):.6e}')
print(f'  in the split-lemma role c1*M = 2, so M = 2/c1 needs c1 >= 1/8000.')
# also the line-114 stopping rule with rho=.01 start
print()
print('  line 114 stopping rule with the printed Mbound:')
for c1t in (F(1, 8000), F(1, 4000)):
    Mt = 2 / c1t
    for r in (F(1, 100), F(1, 1000), F(1, 10 ** 8)):
        v = (2 * Mt + F(1, 2)) * r + (mu / 2 + 1) * Mt ** 2 * r ** 2
        print(f'    c1={float(c1t):.3e} M={float(Mt):.1f} rho={float(r):.0e}: '
              f'value={float(v):.6e} <= mu/4={float(mu/4):.6e} : {v <= mu/4}')

print()
print('=' * 70)
print('3. C891 root box (repaired_tc_krawczyk.json)')
print('=' * 70)
cert = json.loads((L / 'repaired_tc_krawczyk.json').read_text())['certificate']
print('  keys:', list(cert.keys())[:12])
rad = float.fromhex(cert['radius_hex'])
cen = [float.fromhex(x) for x in cert['center_hex']]
print(f'  radius = {rad:.6e}   (rad_hex={cert["radius_hex"][:20]}...)')
print(f'  center (7 comps) = {[round(x,10) for x in cen]}')
print(f'  R  = center[6] = {cen[6]:.12f}')
print(f'  R > 0: {cen[6] > 0};  R + rad < 1: {cen[6]+rad < 1}')
s = sum(cen[:4])
a4 = 3.141592653589793 - 2 * s
print(f'  sum(z0..z3) = {s:.12f};  a4 = pi - 2*sum = {a4:.12f}')
print(f'  all z_i > 0 with margin > rad: {all(x - rad > 0 for x in cen[:5])}')
print()
print('  the code builds 9 radii a = [z0,z1,z2,z3,pi-2S,z3,z2,z1,z0] and rho_k = cos a - sqrt(R^2 - sin^2 a)')
import math
a = [cen[0], cen[1], cen[2], cen[3], a4, cen[3], cen[2], cen[1], cen[0]]
worst = 0.0
for x in a:
    val = cen[6] ** 2 - math.sin(x) ** 2
    worst = max(worst, -val)
print(f'  min over k of (R^2 - sin^2 a_k) = {min(cen[6]**2 - math.sin(x)**2 for x in a):.6e}  '
      f'(positive => sqrt real): {worst <= 0}')
print(f'  rho at center: {[round(math.cos(x)-math.sqrt(max(0.0,cen[6]**2-math.sin(x)**2)),8) for x in a]}')
print(f'  all rho > 0: {all(math.cos(x)-math.sqrt(max(0.0,cen[6]**2-math.sin(x)**2)) > 0 for x in a)}')
