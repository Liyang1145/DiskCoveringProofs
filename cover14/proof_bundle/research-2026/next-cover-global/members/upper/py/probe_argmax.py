"""probe_argmax.py -- debug probe (member upper): which candidate attains R(C)?

Read-only. Prints the top candidates of the exact candidate list with 60-digit
values, the nearest-centre structure of the two twin bisector points of the pair
(8,9), and compares their exact squared distances with the circumcentre value.
"""
import json
import math
import sys
from fractions import Fraction as F

sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
import importlib.util as iu
import pathlib

HERE = pathlib.Path(__file__).resolve().parent
spec = iu.spec_from_file_location('rk', str(HERE / 'repro_c411_independent.py'))
m = iu.module_from_spec(spec)
spec.loader.exec_module(m)

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

print('centres (script order):')
for i, (a, b) in enumerate(C):
    print('  %2d  (%+.20f, %+.20f)' % (i, float(a), float(b)))

P = m.candidates(C)
vals = sorted(((m.f_num(p, C), lab, p) for lab, p in P), key=lambda z: -z[0])
print()
print('top candidates by 60-digit value:')
for v, lab, p in vals[:8]:
    print('  %-22s kind=%-4s val=%s' % (lab, p[0], ('%.60f' % float(v))))

print()
for pt in [(F(0), F(1)), (F(0), F(-1))]:
    d = sorted(((pt[0] - a) ** 2 + (pt[1] - b) ** 2, i) for i, (a, b) in enumerate(C))
    print('point %s nearest centres: %s' % (pt, [(i, float(x)) for x, i in d[:3]]))

bis = [(lab, p) for lab, p in P if lab.startswith('bisector8,9')]
print()
print('bisector8,9 candidates:')
for lab, p in bis:
    _, ux, uy, q, qr, wx, wy, sig = p
    print('  %-20s u=(%.6f,%.6f) q=%.6f qr=%.6f w=(%.6f,%.6f) sigma=%d'
          % (lab, float(ux), float(uy), float(q), float(qr), float(wx), float(wy), sig))

# circumcentre value (exact rational squared distance)
i, j, k = 10, 11, 12
ax, ay = C[j][0] - C[i][0], C[j][1] - C[i][1]
bx, by = C[k][0] - C[i][0], C[k][1] - C[i][1]
D = ax * by - ay * bx
e = (C[j][0] ** 2 + C[j][1] ** 2 - C[i][0] ** 2 - C[i][1] ** 2) / 2
f = (C[k][0] ** 2 + C[k][1] ** 2 - C[i][0] ** 2 - C[i][1] ** 2) / 2
ux, uy = (e * by - f * ay) / D, (ax * f - bx * e) / D
q0 = min((ux - a) ** 2 + (uy - b) ** 2 for a, b in C)
q1 = min((F(0) - a) ** 2 + (F(1) - b) ** 2 for a, b in C)
q2 = min((F(0) - a) ** 2 + (F(-1) - b) ** 2 for a, b in C)
print()
print('circum10,11,12 = (%.20f, %.20f)   q0 = min_i |p*-c_i|^2' % (float(ux), float(uy)))
SC = 10 ** 60
for nm, q in (('q0 (circumcentre)', q0), ('q1 ((0,1) bisector)', q1), ('q2 ((0,-1) bisector)', q2)):
    mm = (q.numerator * SC * SC) // q.denominator
    r = math.isqrt(mm)
    print('  %-22s sqrt = 0.%s' % (nm, str(r)[:60]))
print('  q0 == q1 ?', q0 == q1, '  q0 == q2 ?', q0 == q2, '  q1 == q2 ?', q1 == q2)
print('  q0 < q1 ?', q0 < q1, '   q1 < q0 ?', q1 < q0)
