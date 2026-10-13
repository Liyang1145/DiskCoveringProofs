"""Quantify the damage of the unsound `quad`/`scalar_quad`, and compute what the certificate
total becomes with a sound enclosure.

Bug (lead/certify_q0_closure.py lines 21-32):
    scalar_quad(a,b) must enclose  min_{x in [0,1]} (a x^2 + b x).
    With a >= 0 and b >= 0 it returns [min(0,a+b), max(0,a+b)]  -- correct.
    With b < 0 the true minimum is  min(0, a+b, vertex) and the vertex term
    a x*^2 + b x* = -b^2/(4a) at x* = -b/(2a) in [0,1] is silently DROPPED unless
    (2a+b).b <= 0.  E.g. scalar_quad(0.5,-0.9) = 0.0 while min = -0.405.
    Since quad() feeds every factor's integrand, every "upper" bound built from it is not an
    upper bound.

This script:
  1. demonstrates the bug on the code's own functions,
  2. verifies my sound replacement against dense sampling,
  3. recomputes each factor family's true maximum from the certificate's own coefficients,
  4. recomputes constant + sum of true maxima and compares with pi.
"""
import io, json, math, os, random, sys
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

quad, scalar_quad, interval = ns['quad'], ns['scalar_quad'], ns['interval']
pi = math.pi
R2 = (19 / 50) ** 2
zs = [float(v.a) for v in ns['z']]
faces = [tuple(f) for f in ns['faces']]
edges = [tuple(e) for e in ns['edges']]
adj = ns['adj']
cert = json.loads((LEAD / 'q0_closure_dual_certificate_0_3.json').read_text())
stored = {f['factor']: f['upper'] for f in cert['factors']}

# ---------------------------------------------------------------- 1. the bug
print('=== 1. the code\'s own quad on simple cases (true min of a x^2 + b x on [0,1]) ===')
def true_min_scalar(a, b):
    c = [0.0, a + b]
    if a != 0 and 0 <= -b / (2 * a) <= 1:
        x = -b / (2 * a)
        c.append(a * x * x + b * x)
    return min(c)


for a, b in [(0.5, -0.9), (1.0, -1.5), (0.493277789, -0.419664498), (0.25, -0.24),
             (0.5, 0.2), (0.3, -0.1)]:
    got = scalar_quad(iv.mpf(a), iv.mpf(b))
    tr = true_min_scalar(a, b)
    print(f'  a={a:+.9f} b={b:+.9f}: code=[{float(got.a):+.12f},{float(got.b):+.12f}]  '
          f'true min={tr:+.12f}  encloses? {float(got.a) <= tr <= float(got.b)}')

# ---------------------------------------------------------------- 2. sound replacement
def scalar_quad_fixed(A, B):
    """enclosure of min_{x in [0,1]} (A x^2 + B x) for interval A,B  (sound, simple)"""
    zero = iv.mpf(0)
    cands = [iv.mpf(0)]
    if A.b + B.b > 0:
        cands.append(iv.mpf(0))
    else:
        cands.append(A + B)
    if A.a > 0:
        xlo = interval(max(0.0, min(1.0, float(-B.b / (2 * A.a)))), max(0.0, min(1.0, float(-B.a / (2 * A.b)))))
        if xlo.b < xlo.a:
            xlo = interval(0.0, 1.0)
        xs = [xlo.a, xlo.b, (xlo.a + xlo.b) / 2]
        for x in xs:
            cands.append(A * x * x + B * x)
    return interval(min(float(c.a) for c in cands), max(float(c.b) for c in cands))


def quad_fixed(A, B):
    lo = scalar_quad_fixed(A.a, B.a)
    n = int((B.b - B.a) / max(1e-12, (B.b - B.a) / 8)) if B.b > B.a else 1
    n = max(1, min(8, n))
    tot_lo = None
    for k in range(n + 1):
        y = B.a + (B.b - B.a) * k / n
        cand = scalar_quad_fixed(A, iv.mpf(float(y)))
        tot_lo = cand.a if tot_lo is None else min(tot_lo, float(cand.a))
    return interval(tot_lo, max(float(lo.b), float(scalar_quad_fixed(A, iv.mpf(float(B.b))).b)))


rng = random.Random(3)
bad = 0
worst = None
for _ in range(20000):
    x1 = rng.uniform(-0.6, 0.0)
    A = interval(min(x1, x1 + 0.6), max(x1, x1 + 0.6))
    y1 = rng.uniform(-1.2, -0.1)
    B = interval(min(y1, y1 + 0.4), max(y1, y1 + 0.4))
    got = quad_fixed(A, B)
    true_min = min(float((A * x * x + B * x).a) for x in [i / 60 for i in range(61)])
    if float(got.a) > true_min + 1e-9:
        bad += 1
        if worst is None:
            worst = (A, B, got, true_min)
print(f'\n=== 2. sound replacement: sampled-min violations = {bad}/20000 ===')
if worst:
    print('   example:', worst[0], worst[1], '->', worst[2], 'sampled min', worst[3])

# ---------------------------------------------------------------- 3. true per-factor maxima
def face_coeffs(t):
    f = faces[t]
    co, dd, ll = [], [], []
    for k, i in enumerate(f):
        e = tuple(sorted(j for j in f if j != i))
        ei = edges.index(e)
        co.append(-zs[i] - zs[50 + ei])
        sgn = 1 if adj[e][0][0] == t else -1
        dd.append(sgn * zs[11 + ei]); ll.append(sgn * zs[73 + ei])
    return co, dd, ll


def true_face_max(t, ngrid=4000):
    co, dd, ll = face_coeffs(t)
    best = -1e9
    bestx = None
    N = 300
    for ia in range(N + 1):
        a = pi * ia / N
        for ib in range(N + 1 - ia):
            b = pi * ib / N
            c = pi - a - b
            sn = [math.sin(a), math.sin(b), math.sin(c)]
            V = 2 * R2 * sn[0] * sn[1] * sn[2] + sum(dd[k] * sn[k] ** 2 for k in range(3))
            L = sum(ll[k] * sn[k] for k in range(3))
            r2 = 1.0 if V >= 0 else 0.0
            val = sum(co[k] * (a, b, c)[k] for k in range(3)) + r2 * (V + L)
            if val > best:
                best, bestx = val, (a, b)
    return best, bestx


def switch_coeffs(bi):
    i, j = bi, (bi + 1) % 9
    ei = edges.index(tuple(sorted((i, j))))
    return (zs[i] + zs[j] - zs[50 + ei] + 2 * zs[112 + bi], zs[11 + ei],
            zs[32 + 2 * i + 1] + zs[32 + 2 * j], -zs[73 + ei],
            zs[73 + 2 * i + 1] + zs[73 + 2 * j])


def true_switch_max(bi, N=200000):
    c, d, e, g, h = switch_coeffs(bi)
    best, bestx = -1e9, None
    for k in range(N + 1):
        b = pi / 2 * k / N
        V = R2 * math.sin(2 * b) / 2 + (-d) * math.sin(b) ** 2 + e
        L = g * math.sin(b) + h
        r2 = 1.0 if V >= 0 else 0.0
        val = c * b + r2 * (V + L)
        if val > best:
            best, bestx = val, b
    return best, bestx


def ring_params(i):
    return (zs[i], zs[32 + 2 * i], zs[32 + 2 * i + 1], zs[71] + (zs[72] if i >= 3 else 0),
            zs[73 + 2 * i], zs[73 + 2 * i + 1], zs[112 + i], zs[112 + (i + 1) % 9])


def true_ring_max(i, N=40):
    mu, d, e, C, dl, el, hl, hr = ring_params(i)
    best, bestx = -1e9, None
    for ka in range(N + 1):
        a = pi * ka / N
        for ku in range(N + 1):
            u = ku / N
            for kv in range(N + 1):
                v = kv / N
                q = u * u + v * v - 2 * u * v * math.cos(a)
                if q <= 0:
                    continue
                w = 2 * math.asin(min(1.0, 0.38 * math.sqrt(q) / 2))
                beta = math.atan2(v * math.sin(a), u - v * math.cos(a))
                val = (R2 * u * v * math.sin(a) / 2 + (w - math.sin(w)) / 2 + C * w
                       - mu * a - d * u * u - e * v * v - dl * u - el * v
                       + (hl - hr) * beta - hr * a + hr * pi + (hl + hr) * w / 2)
                if val > best:
                    best, bestx = val, (a, u, v)
    return best, bestx


print('\n=== 3. factor family: certified upper vs true (grid) maximum ===')
tot_true = 0.0
rows = []
for t in range(11):
    v, x = true_face_max(t)
    rows.append((f'face{t}', v, x, stored[f'face{t}']))
for bi in range(9):
    v, x = true_switch_max(bi)
    rows.append((f'switch{bi}', v, x, stored[f'switch{bi}']))
for i in range(9):
    v, x = true_ring_max(i)
    rows.append((f'ring{i}', v, x, stored[f'ring{i}']))
for name, v, x, up in rows:
    tot_true += v
    flag = 'OK ' if v <= up else 'VIOLATED'
    print(f'  {flag} {name:9s} true_max={v:+.9f}  certified_upper={up:.9f}  diff={v - up:+.3e}')
const_part = (pi * (sum(zs[:9]) + 2 * sum(zs[9:11]) + sum(zs[50:71]) - 2 * zs[71] - 2 * zs[72])
              + 2 * zs[72] * math.asin(2 * 0.38) - pi * sum(zs[112:]))
print(f'\n  constant part            = {const_part:+.9f}')
print(f'  sum of true maxima       = {tot_true:+.9f}')
print(f'  corrected total          = {const_part + tot_true:+.9f}')
print(f'  certified total          = {cert["upper"]}')
print(f'  pi                       = {pi:.9f}')
print(f'  corrected total < pi ?   {const_part + tot_true < pi}   (margin {pi - (const_part + tot_true):+.6f})')
json.dump({'certified_total': cert['upper'],
           'corrected_total_grid': const_part + tot_true,
           'per_factor': [{'family': n, 'true_max_grid': v, 'certified_upper': u} for n, v, x, u in rows]},
          open(HERE / 'quad_bug_impact.json', 'w'), indent=2)
print('\nwrote quad_bug_impact.json')
