"""Reconcile: module closure value vs value recomputed from the closure's own captured defaults."""
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

fam = {n: f for n, f, d in ns['factors']}
z = [float(v.a) for v in ns['z']]
R2 = (19 / 50) ** 2
pi = math.pi
quad = ns['quad']

for bi in (0, 1, 3, 4, 8):
    f = fam[f'switch{bi}']
    caps = [float(v.a) for v in f.__defaults__]
    print(f'\n--- switch{bi} ---')
    print('  captured defaults (float, in source order c,d,e,g,h):', [f'{v:+.9f}' for v in caps])
    # source-order formula with the module's own quad()
    c, d, e, g, h = caps
    for b in (0.0, 0.5, pi / 2):
        modv = f([iv.mpf(b)])
        v = R2 * math.sin(2 * b) / 2 - d * math.sin(b) ** 2 + e
        lin = g * math.sin(b) + h
        rec = float((c * iv.mpf(b) + quad(iv.mpf(v), iv.mpf(lin))).a)
        print(f'  b={b:8.6f}: module=[{float(modv.a):+.9f},{float(modv.b):+.9f}]  '
              f'recomputed={rec:+.9f}  min(0,v+lin)={min(0.0, v+lin):+.9f}  '
              f'v={v:+.9f} lin={lin:+.9f}')
    # source-formula parameters, computed here from z
    i, j = bi, (bi + 1) % 9
    ei = ns['edges'].index(tuple(sorted((i, j))))
    src_c = z[i] + z[j] - z[ns['kap'] + ei] + 2 * z[ns['cl'] + bi]
    src_d = z[ns['side'] + ei]
    src_e = z[ns['rr'] + 2 * i + 1] + z[ns['rr'] + 2 * j]
    src_g = -z[ns['lin'] + ei]
    src_h = z[ns['lin'] + 21 + 2 * i + 1] + z[ns['lin'] + 21 + 2 * j]
    print('  source-formula params (c,d,e,g,h):',
          [f'{v:+.9f}' for v in (src_c, src_d, src_e, src_g, src_h)])
    # and the consecutive-index variant that the marker test suggested
    alt_h = z[ns['lin'] + 2 * i + 1] + z[ns['lin'] + 2 * j]
    alt_e = z[ns['rr'] + 2 * i] + z[ns['rr'] + 2 * j]
    print(f'  alt variant e={alt_e:+.9f} h={alt_h:+.9f}')
