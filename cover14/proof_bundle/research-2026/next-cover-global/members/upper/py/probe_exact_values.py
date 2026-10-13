"""probe_exact_values.py -- exact high-precision values of the key candidates.

Read-only. Uses integer arithmetic only (no float in the numbers printed): for each
candidate it evaluates min_i dist(p, c_i) at scale 10^-70 by integer sqrt, so the
digits printed are real digits.  Purpose: decide which candidate attains R(C) and
whether R(C)^2 is rational.
"""
import json
import math
import pathlib
import sys
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import importlib.util as iu

spec = iu.spec_from_file_location('rk', str(HERE / 'repro_c411_independent.py'))
m = iu.module_from_spec(spec)
spec.loader.exec_module(m)

SC = 10 ** 70


def isqrt_scaled(q):
    """sqrt(q) at scale SC as an integer (floor)."""
    mm = (q.numerator * SC * SC) // q.denominator
    return math.isqrt(mm)


def dec(v):
    return '0.' + str(v).rjust(70, '0')[:70]


def show(q, label):
    print('  %-26s %s' % (label, dec(isqrt_scaled(q))))


js = json.loads(m.SRC.read_text(encoding='utf-8'))
th = [F(s) for s in js['th']]
C = []
for j in (0, 2):
    for s in (-1, 1):
        for t in (-1, 1):
            C.append((s * th[j], t * th[j + 1]))
for j in (4, 5):
    C.extend([(th[j], F(0)), (-th[j], F(0))])
C.extend([(F(0), th[6]), (F(0), -th[6])])

i, j, k = 10, 11, 12
ax, ay = C[j][0] - C[i][0], C[j][1] - C[i][1]
bx, by = C[k][0] - C[i][0], C[k][1] - C[i][1]
D = ax * by - ay * bx
e = (C[j][0] ** 2 + C[j][1] ** 2 - C[i][0] ** 2 - C[i][1] ** 2) / 2
f = (C[k][0] ** 2 + C[k][1] ** 2 - C[i][0] ** 2 - C[i][1] ** 2) / 2
ux, uy = (e * by - f * ay) / D, (ax * f - bx * e) / D
q0 = min((ux - a) ** 2 + (uy - b) ** 2 for a, b in C)
argmin0 = min(range(14), key=lambda t: (ux - C[t][0]) ** 2 + (uy - C[t][1]) ** 2)

q1 = min((F(0) - a) ** 2 + (F(1) - b) ** 2 for a, b in C)
q2 = min((F(0) - a) ** 2 + (F(-1) - b) ** 2 for a, b in C)

print('candidate values, 70 digits (integer arithmetic only):')
show(q0, 'circum10,11,12  (rational)')
show(q1, '(0,+1) bisector8,9')
show(q2, '(0,-1) bisector8,9')
print('  json R literal            %s' % js['R'])
print('  C412 stated value         %s' % '0.3317320342762341235155066403893542386599009287817317893317705660612302')
print()
print('exact comparisons (Fractions):')
print('  q0 == q1 :', q0 == q1, '   q0 < q1 :', q0 < q1, '   q1 < q0 :', q1 < q0)
print('  q0 - q1  =', q0 - q1)
print('  q0 - q2  =', q0 - q2)
print('  q0 argmin centre index =', argmin0,
      ' (centre =', [str(z) for z in C[argmin0]], ')')
print()
print('does the literal equal sqrt(q0) or sqrt(q1)?')
lit = F(js['R'])
print('  literal^2 (exact) - q0 =', lit * lit - q0)
print('  literal^2 (exact) - q1 =', lit * lit - q1)
print('  literal == floor70(sqrt(q0)) :', dec(isqrt_scaled(q0)) == js['R'])
print('  literal == floor70(sqrt(q1)) :', dec(isqrt_scaled(q1)) == js['R'])
print()
print('digits 60..70 of each (to separate them):')
print('  sqrt(q0):', dec(isqrt_scaled(q0))[:70])
print('  sqrt(q1):', dec(isqrt_scaled(q1))[:70])
