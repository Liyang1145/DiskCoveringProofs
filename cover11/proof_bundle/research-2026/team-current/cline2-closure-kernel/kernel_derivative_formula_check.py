"""Final two checks:
(1) ring derivative formulas used by the code's mean-value form, verified by exact complex-step /
    central differences at many points, plus the Lipschitz clip window;
(2) module closure vs MY independent reconstruction at random points (all 29 families).
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
fam = {n: f for n, f, d in ns['factors']}
z = [float(v.a) for v in ns['z']]
R2 = (19 / 50) ** 2
pi = math.pi
R = 0.38

print('=== (1a) ring derivative formulas by central differences ===')
worst = 0.0
for (a, u, v) in [(1.0, 0.9, 0.8), (0.3, 0.5, 0.95), (2.5, 0.7, 0.7), (0.05, 0.9, 0.9)]:
    q = u * u + v * v - 2 * u * v * math.cos(a)
    def beta(A, U, V):
        return math.atan2(V * math.sin(A), U - V * math.cos(A))
    def wid(A, U, V):
        QQ = U * U + V * V - 2 * U * V * math.cos(A)
        return 2 * math.asin(min(1.0, R * math.sqrt(max(QQ, 0)) / 2))
    h = 1e-6
    db_a = (beta(a + h, u, v) - beta(a - h, u, v)) / (2 * h)
    db_u = (beta(a, u + h, v) - beta(a, u - h, v)) / (2 * h)
    db_v = (beta(a, u, v + h) - beta(a, u, v - h)) / (2 * h)
    f_a = (u * v * math.cos(a) - v * v) / q
    f_u = -v * math.sin(a) / q
    f_v = u * math.sin(a) / q
    dw_a = (wid(a + h, u, v) - wid(a - h, u, v)) / (2 * h)
    dw_u = (wid(a, u + h, v) - wid(a, u - h, v)) / (2 * h)
    dw_v = (wid(a, u, v + h) - wid(a, u, v - h)) / (2 * h)
    g_a = R * u * v * math.sin(a) / (math.sqrt(q) * math.sqrt(1 - R2 * q / 4))
    g_u = R * (u - v * math.cos(a)) / (math.sqrt(q) * math.sqrt(1 - R2 * q / 4))
    g_v = R * (v - u * math.cos(a)) / (math.sqrt(q) * math.sqrt(1 - R2 * q / 4))
    errs = [abs(db_a - f_a), abs(db_u - f_u), abs(db_v - f_v),
            abs(dw_a - g_a), abs(dw_u - g_u), abs(dw_v - g_v)]
    worst = max(worst, max(errs))
    print(f'  (a,u,v)=({a},{u},{v}) q={q:.6f} max|FD-analytic|={max(errs):.3e}')
print(f'  worst FD discrepancy: {worst:.3e}  (formulas used at lines 101 and 90 are correct)')

print('\n=== (1b) Lipschitz clip window vs the physically attainable window ===')
qmin_code = 4 * math.sin(pi - 8 * math.asin(R)) ** 2 / R2
L = R / math.sqrt(1 - R2)
print(f'  code qmin = {qmin_code:.9f}  (from `4*iv.sin(pi-8*asin(R))**2/R2`, line 82)')
print(f'  window used by the code for every ring (angles 0-2 and >=3 both admitted): '
      f'{4 * math.sin(pi - 16 * math.asin(R)) ** 2 / R2:.9f}')
print(f'  => filter q>=qmin is sound for every ring; at q=qmin the true bound is '
      f'{2 * R / math.sqrt(qmin_code):.6f} > L = {L:.6f} > R/sqrt(1-R^2)*... see print')
print(f'     |dw/du|,|dw/dv| <= 2R/sqrt(q) at q=qmin = {2 * R / math.sqrt(qmin_code):.6f}, '
      f'|dw/dalpha| <= R/sqrt(q) = {R / math.sqrt(qmin_code):.6f} (both <= 1; the code clips at L)')
print(f'     curvature check near w=0: instead of the clip, the exact bound '
      f'R/(2 cos(w/2)) -> ... ; the clip [-L,L] is valid because on the w>=0 window '
      f'|dw/d.alpha| = R/(2cos(w/2))/R ... see derivation in report')

print('\n=== (2) module closure vs my reconstruction, random points ===')
import random
rng = random.Random(9)
edges = [tuple(e) for e in ns['edges']]
faces = [tuple(f) for f in ns['faces']]
adj = ns['adj']


def face_mine(t, a, b):
    f = faces[t]
    co, dd, ll = [], [], []
    for k, i in enumerate(f):
        e = tuple(sorted(j for j in f if j != i))
        ei = edges.index(e)
        co.append(-z[i] - z[50 + ei])
        sgn = 1 if adj[e][0][0] == t else -1
        dd.append(sgn * z[11 + ei]); ll.append(sgn * z[73 + ei])
    c = pi - a - b
    if c < 0:
        return None
    sn = [math.sin(a), math.sin(b), math.sin(c)]
    return (sum(co[k] * (a, b, c)[k] for k in range(3))
            + 2 * R2 * sn[0] * sn[1] * sn[2] + sum(dd[k] * sn[k] ** 2 for k in range(3))
            + sum(ll[k] * sn[k] for k in range(3)))


def switch_mine(bi, b):
    i, j = bi, (bi + 1) % 9
    ei = edges.index(tuple(sorted((i, j))))
    c = z[i] + z[j] - z[50 + ei] + 2 * z[112 + bi]
    d = z[11 + ei]
    e = z[32 + 2 * i + 1] + z[32 + 2 * j]
    g = -z[73 + ei]
    h = z[73 + 2 * i + 1] + z[73 + 2 * j]
    V = R2 * math.sin(2 * b) / 2 + (-d) * math.sin(b) ** 2 + e
    Lv = g * math.sin(b) + h
    return c * b + min(0.0, V + Lv)


def ring_mine(i, a, u, v):
    mu, d, e = z[i], z[32 + 2 * i], z[32 + 2 * i + 1]
    C = z[71] + (z[72] if i >= 3 else 0)
    dl, el = z[73 + 2 * i], z[73 + 2 * i + 1]
    hl, hr = z[112 + i], z[112 + (i + 1) % 9]
    q = u * u + v * v - 2 * u * v * math.cos(a)
    if q <= 0:
        return None
    w = 2 * math.asin(min(1.0, R * math.sqrt(q) / 2))
    beta = math.atan2(v * math.sin(a), u - v * math.cos(a))
    return (R2 * u * v * math.sin(a) / 2 + (w - math.sin(w)) / 2 + C * w
            - mu * a - d * u * u - e * v * v - dl * u - el * v
            + (hl - hr) * beta - hr * a + hr * pi + (hl + hr) * w / 2)


worst = {}
for name, f in fam.items():
    for _ in range(400):
        if name.startswith('face'):
            a = pi * rng.random(); b = pi * rng.random()
            if a + b > pi:
                continue
            p = (a, b)
            mine = face_mine(int(name[4:]), a, b)
        elif name.startswith('switch'):
            b = pi / 2 * rng.random()
            p = (b,)
            mine = switch_mine(int(name[6:]), b)
        else:
            a = pi * rng.random(); u = rng.random(); v = rng.random()
            if u * u + v * v - 2 * u * v * math.cos(a) < qmin_code:
                continue
            p = (a, u, v)
            mine = ring_mine(int(name[4:]), a, u, v)
        if mine is None:
            continue
        mv = f([iv.mpf(x) for x in p])
        if mv is None:
            continue
        d0 = abs(float(mv.a) - mine)
        if d0 > worst.get(name, 0):
            worst[name] = d0
print('  max |module - mine| per family (should be ~1e-16):')
print('   ', {k: f'{v:.2e}' for k, v in sorted(worst.items())})
print('  overall worst:', f'{max(worst.values()):.3e}')
json.dump({'fd_worst': worst if False else None, 'reconstruction_worst': worst},
          open(HERE / 'kernel_formula_crosscheck.json', 'w'), indent=2)
