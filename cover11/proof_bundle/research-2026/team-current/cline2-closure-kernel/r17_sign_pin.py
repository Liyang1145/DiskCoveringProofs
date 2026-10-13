"""R17: pin the sign of the tangent step.

h(T) = -sin(2T). On T in [2, 2 acos(0.375)] = [2, 2.372799], 2T in (pi, 2pi) so
h''(T) = 4 sin(2T) > 0 THERE: h is CONVEX, not concave on that interval.
The doc uses T in [2, 2acos(3/8)]; note acos(3/8) = 1.1863996 and
2 acos(3/8) = 2.372799105 > pi, so sin(2T) < 0 only after 2T > pi, i.e. never here.

Consequences:
  * tangent line lies BELOW h (only touching at tau): h(T) >= h(tau) + h'(tau)(T-tau),
    so -h(T) <= -h(tau) - h'(tau)(T-tau).
  * the kernel's gap g = r^2 [ h(tau) + h'(tau)(T-tau) - h(T) ] is >= 0, so subtracting it
    (as certify_ridge_tangent does) is the WRONG direction for an upper bound on G.
"""
import json, math, sys
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')

b_hi = math.acos(0.375)
T_lo, T_hi = 2.0, 2 * b_hi
print(f'T range = [{T_lo}, {T_hi:.9f}]')
print(f'2T range = [{2*T_lo}, {2*T_hi:.9f}]')
print(f'pi = {math.pi:.9f};  2T > pi for all T in range: {2*T_lo > math.pi}')
print(f'sin(2T) at T=2: {math.sin(4.0):+.9f} ; at T=2.3728: {math.sin(4.7456):+.9f}')
print('=> h\'\'(T) = 4 sin 2T > 0 on the whole interval: h is convex there.')
print()
print('h\'\'(T) at the doc\'s stated interval [2, 2acos(3/8)]:')
print(f'   acos(3/8) = {math.acos(0.375):.9f}; 2*acos(3/8) = {2*math.acos(0.375):.9f}')
print(f'   min over a grid: {min(4*math.sin(2*(T_lo+(T_hi-T_lo)*k/4000)) for k in range(4001)):.6f}')

TAU = 87 / 40
print(f'\ntau = 87/40 = {TAU}; h(tau) = {-math.sin(2*TAU):+.9f}; h\'(tau) = {-2*math.cos(2*TAU):+.9f}')
worst_signed = -9e9
worst_abs = 0.0
arg = None
for k in range(200001):
    T = T_lo + (T_hi - T_lo) * k / 200000
    h = -math.sin(2 * T)
    tang = -math.sin(2 * TAU) - 2 * math.cos(2 * TAU) * (T - TAU)
    d = h - tang
    if d > worst_signed:
        worst_signed, arg = d, T
    worst_abs = max(worst_abs, abs(d))
print(f'max_T [ h(T) - tangent(T) ] = {worst_signed:+.6e} at T={arg:.9f}')
print(f'max_T | h(T) - tangent(T) | = {worst_abs:.6e}')
print('sign > 0 => tangent below h => the bound direction in RIDGE-RANK-ONE-COUPLING.md §11 is inverted.')
print()
print('gap values actually stored in ridge_split_control.json:')
d = json.loads((LEAD / 'ridge_split_control.json').read_text())
if isinstance(d, dict):
    pts = d.get('points', [])
    print(f'  n={d.get("n")}  sympy_trig_identity={d.get("sympy_trig_identity")}')
    for p in pts[:4]:
        print('   tangent_gap =', p.get('tangent_gap'), ' residual =', p.get('residual'))
print()
p = LEAD / 'ridge_tangent_certificate.json'
c = json.loads(p.read_text())
print('certificate keys:', list(c.keys()))
print('scope:', c.get('scope'))
print('upper:', c.get('upper'))
print('constant:', c.get('constant'))
comp = c.get('components')
print('components type/len:', type(comp).__name__, len(comp) if hasattr(comp, '__len__') else '')
if isinstance(comp, list):
    for row in comp[:6]:
        print('   ', row)
print('domain:', c.get('domain'))
print('source_sha256 present:', 'source_sha256' in c)
