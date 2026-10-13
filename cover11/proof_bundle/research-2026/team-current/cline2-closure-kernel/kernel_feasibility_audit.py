"""Kernel feasibility audit, v2 (correct parameter map, verified by marker substitution).

For every factor family of the RUNNING module (preamble executed in this namespace, B&B body
never run, lead tree untouched) we check the *dual feasibility* the certificate relies on:

    min over x in the stated domain of  F(x) >= 0,

where F is the closure's own residual
    face : co.a + max(0, v)*v + max(0, v)*lin   (two branches on alpha = R^2 sin a sin b sin c + dd. sin^2)
    switch: c*b + max(0, v)*(v + g sin b + h)
    ring : the closure expression itself.

Stage 1: dense grid margins.
Stage 2: multistart global minimisation (random + basis + local polish).
Writes join_audit.json.
"""
import io, json, math, os, sys
from contextlib import redirect_stdout
from pathlib import Path

import numpy as np
from mpmath import iv

LEAD = Path(__file__).resolve().parents[1] / 'lead'
HERE = Path(__file__).resolve().parent
os.chdir(LEAD)
sys.path.insert(0, str(LEAD))
sys.argv = ['certify_q0_closure.py', '0', '3']

SRC = (LEAD / 'certify_q0_closure.py').read_text().splitlines(keepends=True)
PRE = ''.join(SRC[:108])
ns = {'__name__': 'iso', '__file__': str(LEAD / 'certify_q0_closure.py')}
with redirect_stdout(io.StringIO()):
    exec(compile(PRE, 'iso', 'exec'), ns)

z = [float(v.a) for v in ns['z']]
R2 = (19 / 50) ** 2
pi = math.pi
faces = [tuple(f) for f in ns['faces']]
edges = [tuple(e) for e in ns['edges']]
adj = ns['adj']
fams = [(n, f, d) for n, f, d in ns['factors']]
print('factors:', [n for n, _, _ in fams])

cert = json.loads((LEAD / 'q0_closure_dual_certificate_0_3.json').read_text())
stored = {f['factor']: f for f in cert['factors']}
dfile = json.loads((LEAD / 'q0_closure_dual_0_3.json').read_text())
print('z file vs certificate coefficients identical:',
      all(abs(a - float(b)) < 5e-10 for a, b in zip(dfile['z'][:70], cert['coefficients'][:70])))


# ---------------------------------------------------------------- independent formulas
def face_params(t):
    f = faces[t]
    co, dd, ll = [], [], []
    for k, i in enumerate(f):
        e = tuple(sorted(j for j in f if j != i))
        ei = edges.index(e)
        co.append(-z[i] - z[50 + ei])
        sgn = 1 if adj[e][0][0] == t else -1
        dd.append(sgn * z[11 + ei])
        ll.append(sgn * z[73 + ei])
    return co, dd, ll


def F_face(t, a, b):
    co, dd, ll = face_params(t)
    c = pi - a - b
    if a < 0 or b < 0 or c < 0:
        return None
    sn = [math.sin(a), math.sin(b), math.sin(c)]
    al = 2 * R2 * sn[0] * sn[1] * sn[2] + sum(dd[k] * sn[k] ** 2 for k in range(3))
    lin = sum(ll[k] * sn[k] for k in range(3))
    return sum(co[k] * (a, b, c)[k] for k in range(3)) + min(0.0, al + lin)


def switch_params(bi):
    i, j = bi, (bi + 1) % 9
    ei = edges.index(tuple(sorted((i, j))))
    c = z[i] + z[j] - z[50 + ei] + 2 * z[112 + bi]
    d = z[11 + ei]
    e = z[32 + 2 * i + 1] + z[32 + 2 * j]
    g = -z[73 + ei]
    h = z[73 + 2 * i + 1] + z[73 + 2 * j]
    return c, d, e, g, h


def F_switch(bi, b):
    c, d, e, g, h = switch_params(bi)
    if b < 0 or b > pi / 2:
        return None
    v = R2 * math.sin(2 * b) / 2 - d * math.sin(b) ** 2 + e
    return c * b + min(0.0, v + g * math.sin(b) + h)


def ring_params(i):
    mu = z[i]
    d = z[32 + 2 * i]
    e = z[32 + 2 * i + 1]
    C = z[71] + (z[72] if i >= 3 else 0)
    dl = z[73 + 2 * i]
    el = z[73 + 2 * i + 1]
    hl = z[112 + i]
    hr = z[112 + (i + 1) % 9]
    return mu, d, e, C, dl, el, hl, hr


def F_ring(i, a, u, v):
    mu, d, e, C, dl, el, hl, hr = ring_params(i)
    if a < 0 or a > pi or u < 0 or v < 0:
        return None
    q = u * u + v * v - 2 * u * v * math.cos(a)
    if q <= 0:
        return None
    w = 2 * math.asin(min(1.0, 19 / 50 * math.sqrt(q) / 2))
    base = R2 * u * v * math.sin(a) / 2 + (w - math.sin(w)) / 2 + C * w
    base -= mu * a + d * u * u + e * v * v + dl * u + el * v
    beta = math.atan2(v * math.sin(a), u - v * math.cos(a))
    # module: extra = (hl-hr)*beta - hr*a + hr*pi + (hl+hr)*w/2   [hl = h_i, hr = h_{i+1}]
    return base + (hl - hr) * beta - hr * a + hr * pi + (hl + hr) * w / 2


# ---------------------------------------------------------------- Stage 1: grid
print('\n=== Stage 1: grid margins (residual >= 0 required) ===')
res = {}
Nf = 200
for t in range(11):
    best = (1e9, None)
    for ia in range(Nf + 1):
        a = pi * ia / Nf
        for ib in range(Nf + 1 - ia):
            b = pi * ib / Nf
            val = F_face(t, a, b)
            if val is not None and val < best[0]:
                best = (val, (a, b))
    res[f'face{t}'] = best
Ns = 2000
for bi in range(9):
    best = (1e9, None)
    for ib in range(Ns + 1):
        b = pi / 2 * ib / Ns
        val = F_switch(bi, b)
        if val is not None and val < best[0]:
            best = (val, (b,))
    res[f'switch{bi}'] = best
Ng = 60
for i in range(9):
    best = (1e9, None)
    for ia in range(Ng + 1):
        a = pi * ia / Ng
        for iu in range(Ng + 1):
            u = iu / Ng
            for ivv in range(Ng + 1):
                v = ivv / Ng
                val = F_ring(i, a, u, v)
                if val is not None and val < best[0]:
                    best = (val, (a, u, v))
    res[f'ring{i}'] = best
for k in sorted(res, key=lambda kk: res[kk][0]):
    print(f'  {k:9s} min={res[k][0]:+.9e} at {tuple(round(x,6) for x in res[k][1])}')
print('worst grid residual =', min(v[0] for v in res.values()))

# ---------------------------------------------------------------- Stage 2: global min
from scipy.optimize import minimize
rng = np.random.default_rng(4242)


def glob_min(fun, bnds, nrand=6000, nlocal=12):
    dim = len(bnds)
    cand = [np.array([(lo + hi) / 2 for lo, hi in bnds])]
    for k in range(dim):
        for fr in (0.0, 1.0, 0.25, 0.75):
            x = np.array([(lo + hi) / 2 for lo, hi in bnds])
            x[k] = bnds[k][0] + fr * (bnds[k][1] - bnds[k][0])
            cand.append(x)
    for _ in range(nrand):
        cand.append(np.array([lo + (hi - lo) * rng.random() for lo, hi in bnds]))
    vals = np.array([fun(x) for x in cand])
    order = np.argsort(vals)
    best = (np.inf, None)
    for k in order[:nlocal]:
        r = minimize(fun, cand[k], method='Nelder-Mead',
                     options={'xatol': 1e-13, 'fatol': 1e-17, 'maxiter': 6000, 'maxfev': 6000})
        if r.fun < best[0]:
            best = (r.fun, r.x)
    return best


print('\n=== Stage 2: global minimisation of each residual ===')
gmin = {}
for t in range(11):
    f = lambda x, t=t: (lambda v: 1e9 if v is None else v)(F_face(t, x[0], x[1]))
    val, x = glob_min(f, [(0, pi), (0, pi)])
    gmin[f'face{t}'] = (val, x)
for bi in range(9):
    f = lambda x, bi=bi: (lambda v: 1e9 if v is None else v)(F_switch(bi, x[0]))
    val, x = glob_min(f, [(0, pi / 2)])
    gmin[f'switch{bi}'] = (val, np.r_[x, [0, 0]])
for i in range(9):
    f = lambda x, i=i: (lambda v: 1e9 if v is None else v)(F_ring(i, x[0], x[1], x[2]))
    val, x = glob_min(f, [(0, pi), (0, 1), (0, 1)])
    gmin[f'ring{i}'] = (val, x)
for k in sorted(gmin, key=lambda kk: gmin[kk][0]):
    print(f'  {k:9s} {gmin[k][0]:+.9e} at {tuple(round(float(v),8) for v in gmin[k][1])}')
print('worst global residual =', min(v[0] for v in gmin.values()))
print('worst family =', min(gmin, key=lambda kk: gmin[kk][0]))

# margin of each claimed B&B upper above the sampled feasible maximum
print('\n=== claimed upper minus sampled minimum (must be positive) ===')
for k in sorted(stored):
    gap = stored[k]['upper'] - gmin[k][0]
    flag = 'OK ' if gap > 0 else 'BAD'
    print(f'  {flag} {k:9s} upper={stored[k]["upper"]:.9f} res_min={gmin[k][0]:+.9e} gap={gap:+.3e}')

json.dump({'grid': {k: [res[k][0], list(map(float, res[k][1]))] for k in res},
           'global': {k: [gmin[k][0], list(map(float, gmin[k][1]))] for k in gmin},
           'stored_upper': {k: stored[k]['upper'] for k in stored}},
          open(HERE / 'kernel_feasibility_numeric.json', 'w'), indent=2)
print('\nwrote kernel_feasibility_numeric.json')
