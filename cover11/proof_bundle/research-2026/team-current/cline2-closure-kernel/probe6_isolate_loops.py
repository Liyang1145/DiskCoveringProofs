"""Execute the switch-loop lines (68-75) and ring-loop lines (76-78) verbatim, in isolation,
and print the computed parameters. Compares directly against the source formula and against
the defaults actually captured by the module's closures."""
import io, json, os, sys
from contextlib import redirect_stdout
from pathlib import Path
from mpmath import iv

HERE = Path(__file__).resolve().parent
LEAD = HERE.parent / 'lead'
SRC = (LEAD / 'certify_q0_closure.py').read_text()
lines = SRC.splitlines(keepends=True)

os.chdir(LEAD)
sys.argv = ['certify_q0_closure.py', '0', '3']

# own preamble copy (lines 1..67 = through the face loop)
PRE = ''.join(lines[:67])
ns = {'__name__': 'iso', '__file__': str(LEAD / 'certify_q0_closure.py')}
with redirect_stdout(io.StringIO()):
    exec(compile(PRE, 'iso', 'exec'), ns)
z = ns['z']
print('z[33],z[36] =', float(z[33].a), float(z[36].a),
      'sum =', float((z[33] + z[36]).a))
print('z[25],z[43] =', float(z[25].a), float(z[43].a))

# now run the switch loop lines verbatim
SW = ''.join(lines[67:75])
ns2 = dict(ns)
with redirect_stdout(io.StringIO()):
    exec(compile(SW, 'sw', 'exec'), ns2)
print('\nswitch loop verbatim -> captured defaults:')
for name, fun, dom in ns2['factors'][11:]:
    print(f'  {name}: ' + ', '.join(
        f'{n}={float(v.a):+.9f}' for n, v in zip(fun.__code__.co_varnames[-5:], fun.__defaults__)))

# what the source formula says those parameters should be
print('\nformula (source lines 69-70) evaluation:')
faces = ns['faces']; edges = ns['edges']; nf = len(faces)
for bi in range(9):
    i, j = bi, (bi + 1) % 9
    ee = edges.index(tuple(sorted((i, j))))
    c = float((z[i] + z[j] - z[ns['kap'] + ee] + 2 * z[ns['cl'] + bi]).a)
    d = float(z[ns['side'] + ee].a)
    e = float((z[ns['rr'] + 2 * i + 1] + z[ns['rr'] + 2 * j]).a)
    g = float(-z[ns['lin'] + ee].a)
    h = float((z[ns['lin'] + 21 + 2 * i + 1] + z[ns['lin'] + 21 + 2 * j]).a)
    print(f'  switch{bi}: ee={ee:2d} c={c:+.9f} d={d:+.9f} e={e:+.9f} g={g:+.9f} h={h:+.9f}')

# ring loop lines verbatim
RG = ''.join(lines[75:78])
ns3 = dict(ns)
with redirect_stdout(io.StringIO()):
    exec(compile(RG, 'rg', 'exec'), ns3)
print('\nring loop setup evaluation (mu,d,e,C,dl,el,hl,hr):')
for i in range(9):
    zz = ns3['z']
    mu = float(zz[i].a); d = float(zz[ns['rr'] + 2 * i].a); e = float(zz[ns['rr'] + 2 * i + 1].a)
    C = float((zz[ns['lam']] + (zz[ns['eta']] if i >= 3 else 0)).a)
    dl = float(zz[ns['lin'] + 21 + 2 * i].a); el = float(zz[ns['lin'] + 21 + 2 * i + 1].a)
    hl = float(zz[ns['cl'] + (i - 1) % 9].a); hr = float(zz[ns['cl'] + i].a)
    print(f'  ring{i}: mu={mu:+.9f} d={d:+.9f} e={e:+.9f} C={C:+.9f} dl={dl:+.9f} el={el:+.9f} hl={hl:+.9f} hr={hr:+.9f}')
