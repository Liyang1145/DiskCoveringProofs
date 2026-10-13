"""Independent-of-my-reconstruction test: minimise the MODULE'S OWN closure functions directly.

If the module's own closure attains a negative value at a point that satisfies the kernel's
stated domain (b in [0,pi/2]; a in [0,pi], u,v in [0,1], q >= qmin), then the certificate's
per-factor upper bound for that factor is below an achievable value -- regardless of whether my
reconstruction matches the code.
"""
import io, json, math, os, sys
from contextlib import redirect_stdout
from pathlib import Path

import numpy as np
from scipy.optimize import minimize
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

fam = {n: f for n, f, d in ns['factors']}
pi = math.pi
qmin = 4 * math.sin(pi - 8 * math.asin(0.38)) ** 2 / 0.38 ** 2
print('qmin =', qmin)
cert = json.loads((LEAD / 'q0_closure_dual_certificate_0_3.json').read_text())
stored = {f['factor']: f['upper'] for f in cert['factors']}


def lo(box, f):
    v = f([iv.mpf(x) for x in box])
    return None if v is None else float(v.a)


def min_switch(bi, nrand=4000):
    f = fam[f'switch{bi}']
    best = (1e9, None)
    for _ in range(nrand):
        b = (pi / 2) * np.random.random()
        v = lo([b], f)
        if v is not None and v < best[0]:
            best = (v, b)
    for k in range(2001):
        b = (pi / 2) * k / 2000
        v = lo([b], f)
        if v is not None and v < best[0]:
            best = (v, b)
    r = minimize(lambda x: lo([x[0]], f), [best[1]], method='Nelder-Mead',
                 options={'xatol': 1e-14, 'fatol': 1e-18})
    v = lo([float(r.x[0])], f)
    if v is not None and v < best[0]:
        best = (v, float(r.x[0]))
    return best


def min_ring(i, nrand=20000):
    f = fam[f'ring{i}']
    rng = np.random.default_rng(7 + i)
    best = (1e9, None)
    for _ in range(nrand):
        a = pi * rng.random(); u = rng.random(); v = rng.random()
        q = u * u + v * v - 2 * u * v * math.cos(a)
        if q < qmin:
            continue
        val = lo([a, u, v], f)
        if val is not None and val < best[0]:
            best = (val, (a, u, v))
    for x0 in ([best[1]] if best[1] else []) + [(pi, 1.0, 1.0), (0.0, 1.0, 1.0), (pi, 1.0, 0.0), (0.0, 0.0, 1.0)]:
        if x0 is None:
            continue
        r = minimize(lambda x: (lambda t: 1e9 if t is None else t)(lo(x, f)), x0, method='Nelder-Mead',
                     options={'xatol': 1e-12, 'fatol': 1e-16, 'maxiter': 4000})
        val = lo(r.x, f)
        if val is not None and val < best[0]:
            best = (val, tuple(float(t) for t in r.x))
    return best


print('\n=== minimum of the MODULE closure itself, per family ===')
print(f'{"family":9s} {"module min":>16s} {"argmin":>34s} {"claimed upper":>14s}  verdict')
bad = []
for bi in range(9):
    m, x = min_switch(bi)
    up = stored[f'switch{bi}']
    verdict = 'OK' if m >= -1e-12 else 'NEGATIVE'
    if m < -1e-12:
        bad.append((f'switch{bi}', m, x, up))
    print(f'switch{bi:<3d} {m:+16.9f} {str(tuple(round(float(t),8) for t in np.r_[x])):>34s} {up:14.9f}  {verdict}')
for i in range(9):
    m, x = min_ring(i)
    up = stored[f'ring{i}']
    verdict = 'OK' if m >= -1e-12 else 'NEGATIVE'
    if m < -1e-12:
        bad.append((f'ring{i}', m, x, up))
    print(f'ring{i:<4d} {m:+16.9f} {str(tuple(round(float(t),8) for t in x)):>34s} {up:14.9f}  {verdict}')

print('\nnegative families:', [b[0] for b in bad])
json.dump([{'family': b[0], 'module_min': b[1], 'argmin': list(map(float, b[2])),
            'claimed_upper': b[3]} for b in bad],
          open(HERE / 'module_closure_negatives.json', 'w'), indent=2)
print('wrote module_closure_negatives.json')
