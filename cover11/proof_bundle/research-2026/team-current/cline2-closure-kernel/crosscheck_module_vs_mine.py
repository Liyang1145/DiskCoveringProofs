"""Cross-check: evaluate MY independent residual formulas against the RUNNING module's own
closure functions at the same points (plus a fine scan of the switch family and ring corners).

If the module's closure is (much) larger than my formula, my reconstruction is wrong;
if they agree and both go negative at feasible points, the certificate's dual is infeasible
on those boxes.
"""
import io, json, math, os, sys
from contextlib import redirect_stdout
from pathlib import Path

from mpmath import iv

LEAD = Path(__file__).resolve().parents[1] / 'lead'
HERE = Path(__file__).resolve().parent
os.chdir(LEAD)
sys.path.insert(0, str(LEAD))
sys.argv = ['certify_q0_closure.py', '0', '3']
SRC = (LEAD / 'certify_q0_closure.py').read_text().splitlines(keepends=True)
ns = {'__name__': 'iso', '__file__': str(LEAD / 'certify_q0_closure.py')}
with redirect_stdout(io.StringIO()):
    exec(compile(''.join(SRC[:108]), 'iso', 'exec'), ns)

z = [float(v.a) for v in ns['z']]
R2 = (19 / 50) ** 2
pi = math.pi
faces = [tuple(f) for f in ns['faces']]
edges = [tuple(e) for e in ns['edges']]
adj = ns['adj']
fam = {n: (f, d) for n, f, d in ns['factors']}

import kernel_feasibility_audit as K   # reuses my formulas (module import only defines funcs)
print('my formula module loaded')


def mod_switch(bi, b):
    f, dom = fam[f'switch{bi}']
    return f([iv.mpf(x) for x in (b,)])


def mod_ring(i, a, u, v):
    f, dom = fam[f'ring{i}']
    return f([iv.mpf(x) for x in (a, u, v)])


print('\n=== switch family: module closure vs my formula at the suspect points ===')
for bi in range(9):
    for b in [0.0, 1.0, pi / 4, pi / 2]:
        mv = mod_switch(bi, b)
        mine = K.F_switch(bi, b)
        print(f'  switch{bi} b={b:8.5f}: module=[{float(mv.a):+.9f},{float(mv.b):+.9f}] '
              f'mine={mine:+.9f}  agree={abs(float(mv.a)-mine) < 1e-9}')

print('\n=== switch0 residual scan (both sources) ===')
worst = (1e9, None)
for k in range(10001):
    b = pi / 2 * k / 10000
    mine = K.F_switch(0, b)
    if mine < worst[0]:
        worst = (mine, b)
print(f'  min over b in [0,pi/2]: mine={worst[0]:+.9f} at b={worst[1]:.6f}')
mv = mod_switch(0, worst[1])
print(f'  module at that b      : [{float(mv.a):+.9f},{float(mv.b):+.9f}]')
print(f'  certificate says switch0 <= {json.loads((LEAD / "q0_closure_dual_certificate_0_3.json").read_text())["factors"][11]["upper"]:.9f}')

print('\n=== ring family: module vs my formula at the grid minima ===')
tests = {
    'ring0': (0.0, 0.9833333333333333, 1.0),
    'ring2': (0.0, 1.0, 0.9833333333333333),
    'ring7': (0.0, 1.0, 0.9833333333333333),
    'ring3': (pi, 1.0, 0.0),
}
for name, (a, u, v) in tests.items():
    i = int(name[4:])
    mv = mod_ring(i, a, u, v)
    mine = K.F_ring(i, a, u, v)
    print(f'  {name} at ({a:.6f},{u:.6f},{v:.6f}): module=[{float(mv.a):+.9f},{float(mv.b):+.9f}] '
          f'mine={mine:+.9f} agree={abs(float(mv.a)-mine) < 1e-9}')

print('\n=== is the ring domain filter actually excluding those points? ===')
qmin = 4 * math.sin(pi - 8 * math.asin(0.38)) ** 2 / 0.38 ** 2
print('  qmin (from the code formula) =', qmin)
for name, (a, u, v) in tests.items():
    q = u * u + v * v - 2 * u * v * math.cos(a)
    print(f'  {name}: q={q:.9f}  q>=qmin? {q >= qmin}  so the filter does NOT exclude it')
