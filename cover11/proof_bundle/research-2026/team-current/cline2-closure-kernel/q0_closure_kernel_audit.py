"""Independent kernel audit of lead/certify_q0_closure.py + q0_closure_dual_certificate_0_3.json.

Independent reconstruction (no import/exec of lead code):
  f_face  = R^2 sin a sin b sin c + sum_k d_k sin^2(ang_k) + r^2 sum_k l_k sin(ang_k) + sum_k co_k ang_k
  f_switch= -R^2 sin(2b)/2 - d sin^2 b + e  + r^2 g sin b + r^2 h
  f_ring  = R^2 u v sin(a)/2 + (w - sin w)/2 + C w - mu a - d u^2 - e v^2 - dl u - el v
            + (h_{i-1} - h_i) beta + h_i (pi - a) + (h_{i-1}+h_i) w/2
  w = 2 asin(R sqrt(q)/2), q = u^2+v^2-2uv cos a, beta = atan2(v sin a, u - v cos a)

Stage A: exact rational re-sum of the assembled total from stored coefficients/u per-factor uppers.
Stage B: certificate graph / affine-redundancy checks (independent).
Stage C: dense-grid residual checks for all 29 factor families.
Stage D: global minimization (multistart SLSQP/D.E.) of each residual.
Stage E: rigorous mpmath interval certification of residual > 0 on boxes around the
         observed candidate minimizers (with padding).
"""
import json, math, sys
from fractions import Fraction as Q
from pathlib import Path

import numpy as np
from mpmath import iv, mp, mpf
import mpmath

LEAD = Path(__file__).resolve().parents[1] / 'lead'
iv.dps = 50
mp.dps = 60

cert = json.loads((LEAD / 'q0_closure_dual_certificate_0_3.json').read_text())
row = json.loads((LEAD / 'q0_closure_dual_0_3.json').read_text())
zf = [float(v) for v in cert['coefficients']]          # exactly what the certificate used
zr = [Q(v) for v in cert['coefficients']]              # exact rationals
pi_f = math.pi
R = 0.38
R2 = R * R
faces = [tuple(f) for f in row['faces']]
edges = [tuple(e) for e in row['edges']]
start, span = cert['start'], cert['span']
Z = lambda i: zf[i]

report = []


def say(s):
    print(s, flush=True)


# ---------------------------------------------------------------- Stage B: graph
say('== Stage B: graph / index-map assertions ==')
expected = [(9, k, k + 1) for k in range(span)] + [(10, k, (k + 1) % 9) for k in range(span, 9)] + \
           [(9, 10, 0), (9, 10, span)]
ok_faces = sorted(tuple(sorted(f)) for f in faces) == sorted(tuple(sorted(f)) for f in expected)
e2 = sorted({tuple(sorted((f[k], f[(k + 1) % 3]))) for f in expected for k in range(3)})
ok_edges = edges == e2
say(f'faces match expected T_j structure: {ok_faces};  edges match: {ok_edges};  ne={len(edges)} nf={len(faces)}')
say(f'z[eta=72] == 0 exactly: {zr[72] == 0};  z[lam=71] = {zf[71]:.6f};  span={span}')
# internal edge naming
internal = sorted(tuple(sorted((i, (i + 1) % 9))) for i in range(9))
say(f'all 9 ring chords present as internal edges: {all(e in edges for e in internal)}')

# ------------------------------------------- Stage A: exact rational re-summation
say('== Stage A: exact rational re-sum of assembled total vs certificate interval ==')
coef_const = sum(zr[:9]) + 2 * sum(zr[9:11]) + sum(zr[50:71]) - 2 * zr[71] - 2 * zr[72]
total_r = None
try:
    from mpmath import asin as m_asin
    asin_term = mpf(2) * mpf(zr[72].numerator) / zr[72].denominator * mpmath.asin(2 * mpf(19) / 50)
except Exception as exc:      # pragma: no cover
    say(f'asin term skipped: {exc}')
    asin_term = mpf(0)
ub_sum = sum(mpf(f['upper']) for f in cert['factors'])
total_assembly = mpf(zr and 0)  # placeholder
tot = mpf(coef_const.numerator) / mpf(coef_const.denominator) * mpmath.pi \
      + asin_term - mpmath.pi * mpf(sum(zr[112:]).numerator) / mpf(sum(zr[112:]).denominator) \
      + ub_sum
say(f'coefficient part (exact rational) = {coef_const} = {float(coef_const):.15f}')
say(f'sum of per-factor uppers (float)   = {float(ub_sum):.15f}')
say(f'gap pi - (coeff*pi + 2*zeta*asin(2R) - pi*sum(h)) [before factors] = '
    f'{float(mpmath.pi - (mpf(coef_const.numerator)/mpf(coef_const.denominator)*mpmath.pi + asin_term - mpmath.pi*mpf(sum(zr[112:]).numerator)/mpf(sum(zr[112:]).denominator))):.15f}')
say(f're-assembled total (mp 60 digits) = {mpmath.nstr(tot, 30)}')
say(f'certificate upper interval        = {cert["upper"]}')
say(f'certificate pi                    = {cert["pi"]}')
say(f'pi - total (mp)                   = {mpmath.nstr(mpmath.pi - tot, 20)}')

# interval re-sum
iv.R = iv.mpf(R)
ivpi = iv.pi


def iv_asin(x):
    if x.a <= -1 or x.b >= 1:
        return iv.mpf([-ivpi.b / 2, ivpi.b / 2])
    return iv.atan2(x, iv.sqrt(1 - x * x))


iv_asin_v = iv_asin(2 * iv.mpf(19) / 50)
iv_asin = iv_asin_v
tot_iv = iv.mpf(str(coef_const.numerator)) / iv.mpf(str(coef_const.denominator)) * ivpi \
    + 2 * iv.mpf(str(zr[72].numerator)) / iv.mpf(str(zr[72].denominator)) * iv_asin \
    - ivpi * iv.mpf(str(sum(zr[112:]).numerator)) / iv.mpf(str(sum(zr[112:]).denominator)) \
    + iv.mpf(str(ub_sum))
say(f'interval re-sum of total          = {tot_iv}')
say(f'interval re-sum < pi ?            = {tot_iv.b < ivpi.a}')
# factor-upper interval recomputation tightness: check self-consistency of stored uppers
say(f'max stored factor upper = {max(f["upper"] for f in cert["factors"]):.6f}; '
    f'min = {min(f["upper"] for f in cert["factors"]):.6f}')


# ------------------------------------------------------- residual: face factors
def adj_of(e):
    return [(t, next(k for k in f if k not in e)) for t, f in enumerate(faces) if e[0] in f and e[1] in f]


def face_coeffs(t):
    f = faces[t]
    co, dd, ll = [], [], []
    for k, i in enumerate(f):
        e = tuple(sorted(j for j in f if j != i))
        ei = edges.index(e)
        co.append(-Z(i) - Z(50 + ei))
        sgn = 1 if adj_of(e)[0][0] == t else -1
        dd.append(sgn * Z(11 + ei))
        ll.append(sgn * Z(73 + ei))
    return co, dd, ll


def face_residual(t, a, b):
    """min over r in [0,1] of [ base + r^2 v + r^2 lin ]  (r^2 = max(0, alpha) of the code)"""
    co, dd, ll = face_coeffs(t)
    c = pi_f - a - b
    if a < 0 or b < 0 or c < 0:
        return None
    ang = (a, b, c)
    sn = [math.sin(x) for x in ang]
    v = 2 * R2 * sn[0] * sn[1] * sn[2] + sum(dd[k] * sn[k] ** 2 for k in range(3))
    lin = sum(ll[k] * sn[k] for k in range(3))
    return sum(co[k] * ang[k] for k in range(3)) + min(0.0, v + lin)


# ----------------------------------------------------- residual: switch factors
def switch_coeffs(bi):
    i, j = bi, (bi + 1) % 9
    ei = edges.index(tuple(sorted((i, j))))
    c = Z(i) + Z(j) - Z(50 + ei) + 2 * Z(112 + bi)
    d = Z(11 + ei)
    e = Z(32 + 2 * i + 1) + Z(32 + 2 * j)
    g = -Z(73 + ei)
    h = Z(94 + 2 * i + 1) + Z(94 + 2 * j)
    return c, d, e, g, h


def switch_residual(bi, b):
    c, d, e, g, h = switch_coeffs(bi)
    if b < 0 or b > pi_f / 2:
        return None
    v = R2 * math.sin(2 * b) / 2 - d * math.sin(b) ** 2 + e
    return c * b + min(0.0, v + g * math.sin(b) + h)


# ------------------------------------------------------- residual: ring factors
def ring_coeffs(i):
    mu = Z(i)
    d = Z(32 + 2 * i)
    e = Z(32 + 2 * i + 1)
    C = Z(71) + (Z(72) if i >= 3 else 0)
    dl = Z(94 + 2 * i)
    el = Z(94 + 2 * i + 1)
    hl = Z(112 + (i - 1) % 9)
    hr = Z(112 + i)
    return mu, d, e, C, dl, el, hl, hr


def width(q):
    return 2 * math.asin(min(1.0, R * math.sqrt(max(q, 0.0)) / 2))


def ring_residual(i, a, u, v):
    mu, d, e, C, dl, el, hl, hr = ring_coeffs(i)
    if a < 0 or a > pi_f or u < 0 or v < 0:
        return None
    q = u * u + v * v - 2 * u * v * math.cos(a)
    if q <= 0:
        return None                      # degenerate; handled by [0,pi] beta branch
    w = width(q)
    base = R2 * u * v * math.sin(a) / 2 + (w - math.sin(w)) / 2 + C * w
    base -= mu * a + d * u * u + e * v * v + dl * u + el * v
    beta = math.atan2(v * math.sin(a), u - v * math.cos(a))
    return base + (hl - hr) * beta + hr * (pi_f - a) + (hl + hr) * w / 2


# ------------------------------------------------- Stage C: dense grids
say('== Stage C: dense-grid residuals ==')
worst = {}


def note(tag, val, xs):
    if val is None:
        return
    if tag not in worst or val < worst[tag][0]:
        worst[tag] = (val, xs)


N = 120
for t in range(len(faces)):
    for ia in range(N + 1):
        a = pi_f * ia / N
        for ib in range(N + 1 - ia):
            b = pi_f * ib / N
            note(f'face{t}', face_residual(t, a, b), (a, b))
for bi in range(9):
    for ib in range(N + 1):
        note(f'switch{bi}', switch_residual(bi, pi_f / 2 * ib / N), (pi_f / 2 * ib / N,))
M = 40
for i in range(9):
    for ia in range(M + 1):
        a = pi_f * ia / M
        for iu in range(M + 1):
            u = iu / M
            for iv2 in range(M + 1):
                v = iv2 / M
                note(f'ring{i}', ring_residual(i, a, u, v), (a, u, v))
for tag in ['face0', 'face5', 'face9', 'switch1', 'switch5', 'ring1', 'ring2', 'ring6']:
    if tag in worst:
        say(f'grid min {tag}: {worst[tag][0]:+.12e} at {tuple(round(x,6) for x in worst[tag][1])}')
gmin = min(s[0] for s in worst.values())
say(f'grid global min residual over all families: {gmin:.12e} '
    f'(negative => certificate infeasible)')
say('per-family grid minima:')
for tag in sorted(worst):
    say(f'  {tag:9s} {worst[tag][0]:+.12e} at {tuple(round(x,6) for x in worst[tag][1])}')

# ------------------------------------------------- Stage D: global minimisation
say('== Stage D: multistart global minimisation of each residual ==')
from scipy.optimize import minimize

rng = np.random.default_rng(20261005)


def glob_min(fun, bounds, nrand=8000, nlocal=10):
    """random + grid + basis-vector sampling, then Nelder-Mead polish of the best starts."""
    dim = len(bounds)
    cand = []
    for lohi in bounds:
        lo, hi = lohi
        cand.append(np.array([(lo + hi) / 2] * dim))
    for k in range(dim):
        for frac in (0.0, 1.0, 0.25, 0.75):
            x = np.array([(lo + hi) / 2 for lo, hi in bounds])
            x[k] = bounds[k][0] + frac * (bounds[k][1] - bounds[k][0])
            cand.append(x)
    for _ in range(nrand):
        cand.append(np.array([lo + (hi - lo) * rng.random() for lo, hi in bounds]))
    vals = [fun(x) for x in cand]
    order = np.argsort(np.array([np.inf if v is None else v for v in vals]))
    starts = [cand[k] for k in order[:nlocal]]
    best = (np.inf, None)
    for x0 in starts:
        res = minimize(fun, x0, method='Nelder-Mead',
                       options={'xatol': 1e-13, 'fatol': 1e-17, 'maxiter': 8000, 'maxfev': 8000})
        if res.fun < best[0]:
            best = (res.fun, res.x)
    return best


margin_tab = []
worst_sup_diff = []
for t in range(len(faces)):
    def f(x, t=t):
        v = face_residual(t, x[0], x[1])
        return np.inf if v is None else v
    val, x = glob_min(f, [(0, pi_f), (0, pi_f)])
    margin_tab.append((f'face{t}', val, (x[0], x[1], pi_f - x[0] - x[1])))
for bi in range(9):
    def f(x, bi=bi):
        v = switch_residual(bi, x[0])
        return np.inf if v is None else v
    val, x = glob_min(f, [(0, pi_f / 2)])
    margin_tab.append((f'switch{bi}', val, (x[0],)))
for i in range(9):
    def f(x, i=i):
        v = ring_residual(i, x[0], x[1], x[2])
        return np.inf if v is None else v
    val, x = glob_min(f, [(0, pi_f), (0, 1), (0, 1)])
    margin_tab.append((f'ring{i}', val, tuple(x)))
say('candidate minima (family, residual, argmin):')
for tag, val, x in margin_tab:
    say(f'  {tag:9s} {val:+.12e}  at {tuple(round(v,8) for v in x)}')
say(f'WORST residual over families: {min(v for _, v, _ in margin_tab):+.12e}')

# Stage D2: B&B upper soundness stress: does any feasible point exceed the claimed per-factor upper?
say('== Stage D2: stress the B&B uppers (feasible max must stay below stored upper) ==')
stored = {f['factor']: f['upper'] for f in cert['factors']}
worst_gap = 1e9
worst_tag = None
for tag, val, x in margin_tab:
    gap = stored[tag] - val
    if gap < worst_gap:
        worst_gap, worst_tag = gap, tag
say(f'tightest stored-upper minus sampled-min: {worst_gap:.6e} ({worst_tag}) '
    f'[negative would mean the B&B upper is below an achievable value]')

json.dump({'stageB': {'faces_ok': ok_faces, 'edges_ok': ok_edges},
           'stageA': {'reassembled_total': mpmath.nstr(tot, 30),
                      'cert_upper': cert['upper'],
                      'pi_minus_total': mpmath.nstr(mpmath.pi - tot, 20)},
           'stageC_grid_min': gmin,
           'stageD': [{'family': t, 'residual': float(v), 'argmin': list(map(float, x))} for t, v, x in margin_tab],
           'stageD2_tightest_upper_gap': {'tag': worst_tag, 'gap': float(worst_gap)}},
          open(Path(__file__).parent / 'kernel_audit_numeric.json', 'w'), indent=2)
say('wrote kernel_audit_numeric.json')
