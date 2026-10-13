"""R20-AREA-LOCALIZE (internal debug for EXACT-AREA-ASSEMBLY-AUDIT.md): locate which bookkeeping
makes the identity exact.  NOT the deliverable (the audit file carries the algebraic derivation);
this only localizes terms so the derivation is not published with a wrong assignment.
"""
import json
import math
from pathlib import Path

HERE = Path(__file__).parent
ALT = HERE.parent / 'r20-alternative' / 'socp_anchor_export.json'
o = json.loads(ALT.read_text(encoding='utf-8'))
U = [tuple(p) for p in o['U']]
C = [tuple(p) for p in o['C_sites']]
Z = [tuple(p) for p in o['Z_aux']]
R = float(o['V'])
FACES = [(9, 0, 1), (9, 1, 2), (9, 2, 3), (9, 3, 4), (10, 4, 5), (10, 5, 6), (10, 6, 7),
         (10, 7, 8), (10, 8, 0), (9, 10, 0), (9, 10, 4)]


def dist(a, b): return math.hypot(a[0] - b[0], a[1] - b[1])
def area3(a, b, c): return abs((b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])) / 2
def cross(a, b, c): return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


print('R (oracle V) =', R)
Afaces = [area3(C[f[0]], C[f[1]], C[f[2]]) for f in FACES]
Asw = [area3(C[i], C[(i + 1) % 9], U[i]) for i in range(9)]
sec = [1 / 2 * dist(C[i], U[(i - 1) % 9]) * dist(C[i], U[i]) *
       math.sin(abs(math.atan2(*[y for y in (U[i][1] - C[i][1], U[i][0] - C[i][0])])) * 0 + 1)
       for i in range(9)]
# sector angle via the cross/dot formula (avoid the messy line above)
sec = []
for i in range(9):
    a = ((U[(i - 1) % 9][0] - C[i][0]), (U[(i - 1) % 9][1] - C[i][1]))
    b = ((U[i][0] - C[i][0]), (U[i][1] - C[i][1]))
    ang = math.acos(max(-1, min(1, (a[0] * b[0] + a[1] * b[1]) / (math.hypot(*a) * math.hypot(*b)))))
    sec.append(0.5 * math.hypot(*a) * math.hypot(*b) * math.sin(ang))
w = []
for i in range(9):
    u0, u1 = U[(i - 1) % 9], U[i]
    w.append(math.atan2(abs(cross((0, 0), u0, u1)), u0[0] * u1[0] + u0[1] * u1[1]))
seg = [(wi - math.sin(wi)) / 2 for wi in w]
print('sum faces   = %.15f' % sum(Afaces))
print('sum switch  = %.15f' % sum(Asw))
print('sum sector  = %.15f' % sum(sec))
print('sum segment = %.15f' % sum(seg))
print('sum caps    = %.15f' % (sum(sec) + sum(seg)))
print('TOTAL faces+switch+sector+segment = %.15f   pi = %.15f   diff = %.3e'
      % (sum(Afaces) + sum(Asw) + sum(sec) + sum(seg), math.pi,
         sum(Afaces) + sum(Asw) + sum(sec) + sum(seg) - math.pi))
# circumradius identity check per face
print()
print('per-face: 2 rho^2 prod sin vs area (obtuse handling)')
for t, f in enumerate(FACES):
    a, b, c = C[f[0]], C[f[1]], C[f[2]]
    ds = [dist(b, c), dist(a, c), dist(a, b)]
    A = area3(a, b, c)
    rho = ds[0] * ds[1] * ds[2] / (4 * A) if A > 0 else float('nan')
    ang = [math.acos(max(-1, min(1, (v[0] * w2[0] + v[1] * w2[1]) / (math.hypot(*v) * math.hypot(*w2)))))
           for v, w2 in ((((c[0] - a[0]), (c[1] - a[1])), ((b[0] - a[0]), (b[1] - a[1]))),
                         (((a[0] - b[0]), (a[1] - b[1])), ((c[0] - b[0]), (c[1] - b[1]))),
                         (((a[0] - c[0]), (a[1] - c[1])), ((b[0] - c[0]), (b[1] - c[1]))))]
    val = 2 * rho ** 2 * math.prod(math.sin(x) for x in ang)
    print('  face%2d area=%.12f  2rho^2 prod=%.12f  diff=%.2e  obtuse=%s'
          % (t, A, val, val - A, any(x > math.pi / 2 for x in ang)))
# Voronoi pairing vs switch triangles
print()
VP = []
for i in range(9):
    j = (i + 1) % 9
    d = dist(C[i], C[j]); a = d / 2
    VP.append((i, a * dist(Z[i], U[i]) if True else 0.0))
print('candidate Voronoi-pairing terms (a*|z_i U_i|):', [round(x, 8) for _, x in VP])
print('sum = %.15f ; sum switches = %.15f ; difference = %.3e'
      % (sum(x for _, x in VP), sum(Asw), sum(x for _, x in VP) - sum(Asw)))
print('  (z_i = face circumcenter of the ring-ring face: check z vs Z_aux)')
print('Z_aux =', [(round(p[0], 6), round(p[1], 6)) for p in Z])
