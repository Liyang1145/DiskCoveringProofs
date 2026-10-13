"""Tiny, decisive module-closure inspection with full intervals printed."""
import io, json, math, os, sys
from contextlib import redirect_stdout
from pathlib import Path
from mpmath import iv

LEAD = Path(__file__).resolve().parents[1] / 'lead'
os.chdir(LEAD)
sys.path.insert(0, str(LEAD))
sys.argv = ['certify_q0_closure.py', '0', '3']
SRC = (LEAD / 'certify_q0_closure.py').read_text().splitlines(keepends=True)
ns = {'__name__': 'iso', '__file__': str(LEAD / 'certify_q0_closure.py')}
with redirect_stdout(io.StringIO()):
    exec(compile(''.join(SRC[:108]), 'iso', 'exec'), ns)

fam = {n: (f, d) for n, f, d in ns['factors']}
z = [float(v.a) for v in ns['z']]
pi = math.pi

print('module constants: quad, scalar_quad, interval present:',
      [k in ns for k in ('quad', 'scalar_quad', 'interval', 'pos')])

for bi in (0, 1, 4):
    f, dom = fam[f'switch{bi}']
    names = f.__code__.co_varnames[-5:]
    dfl = dict(zip(names, f.__defaults__))
    print(f'\n--- switch{bi} closure defaults ---')
    for k, v in dfl.items():
        print(f'   {k} = {v}')
    for b in (0.0, 0.5, pi / 2):
        val = f([iv.mpf(b)])
        print(f'   f({b:.6f}) = [{float(val.a):+.9f}, {float(val.b):+.9f}]')

print('\n--- direct algebra from the printed defaults (switch0) ---')
f, _ = fam['switch0']
names = f.__code__.co_varnames[-5:]
d = dict(zip(names, f.__defaults__))
c = float(d['c'].a); dd = float(d['d'].a); e = float(d['e'].a)
g = float(d['g'].a); h = float(d['h'].a)
R2 = (19 / 50) ** 2
for b in (0.0, 0.5, pi / 2):
    v = R2 * math.sin(2 * b) / 2 - dd * math.sin(b) ** 2 + e
    lin = g * math.sin(b) + h
    q = extra = None
    print(f'   b={b:.6f}: r^2part={v:+.9f} lin={lin:+.9f} min(0,r2+lin)={min(0.0, v+lin):+.9f}'
          f' -> c*b+min = {c * b + min(0.0, v + lin):+.9f}')
    print(f'      note: quad(v,lin) at a POINT should equal min(0, v+lin) = {min(0.0, v + lin):+.9f}')
    print(f'      module quad(v, lin) = {ns["quad"](iv.mpf(v), iv.mpf(lin))}')

print('\n--- ring0 closure at a few interior points (module only) ---')
f, _ = fam['ring0']
for (a, u, v) in [(1.0, 0.9, 0.9), (0.5, 0.5, 0.9), (2.0, 1.0, 1.0), (1.5, 0.5, 0.5)]:
    val = f([iv.mpf(a), iv.mpf(u), iv.mpf(v)])
    print(f'   ring0({a},{u},{v}) = {val}')
