"""Decisive per-factor check with SOURCE-INDEX formulas (lead-corrected), then fix the verdict.

switch: c=z[i]+z[j]-z[50+ee]+2z[112+bi]; d=z[11+ee]; e=z[32+2i+1]+z[32+2j];
        g=-z[73+ee]; h=z[73+21+2i+1]+z[73+21+2j]      (source line 70 literal)
ring  : hl=z[112+(i-1)%9], hr=z[112+i]; dl=z[73+21+2i], el=z[73+21+2i+1]; C=z[71]+(z[72] if i>=3)
Comparison: module closure value at random points vs this formula.
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

fam = {n: f for n, f, d in ns['factors']}
z = [float(v.a) for v in ns['z']]
edges = [tuple(e) for e in ns['edges']]
R2 = (19 / 50) ** 2
R = 0.38
pi = math.pi


def switch_src(bi, b):
    i, j = bi, (bi + 1) % 9
    ei = edges.index(tuple(sorted((i, j))))
    c = z[i] + z[j] - z[50 + ei] + 2 * z[112 + bi]
    d = z[11 + ei]
    e = z[32 + 2 * i + 1] + z[32 + 2 * j]
    g = -z[73 + ei]
    h = z[73 + 21 + 2 * i + 1] + z[73 + 21 + 2 * j]
    V = R2 * math.sin(2 * b) / 2 - d * math.sin(b) ** 2 + e
    lin = g * math.sin(b) + h
    # code: c*b + max_{s in [0,1]}(V s^2 + lin s)
    cands = [0.0, V + lin]
    if V > 0 and 0 <= -lin / (2 * V) <= 1:
        x = -lin / (2 * V)
        cands.append(V * x * x + lin * x)
    return c * b + max(cands)


def ring_src(i, a, u, v):
    mu, d, e = z[i], z[32 + 2 * i], z[32 + 2 * i + 1]
    C = z[71] + (z[72] if i >= 3 else 0)
    dl, el = z[73 + 21 + 2 * i], z[73 + 21 + 2 * i + 1]
    hl, hr = z[112 + (i - 1) % 9], z[112 + i]
    q = u * u + v * v - 2 * u * v * math.cos(a)
    if q <= 0:
        return None
    w = 2 * math.asin(min(1.0, R * math.sqrt(q) / 2))
    beta = math.atan2(v * math.sin(a), u - v * math.cos(a))
    return (R2 * u * v * math.sin(a) / 2 + (w - math.sin(w)) / 2 + C * w
            - mu * a - d * u * u - e * v * v - dl * u - el * v
            + (hl - hr) * beta - hr * a + hr * pi + (hl + hr) * w / 2)


rng = random.Random(17)
print(f'{"family":9s} {"max|module-mine|":>18s}   (over 300 random domain points)')
worst_all = 0.0
for name, f in fam.items():
    worst = 0.0
    for _ in range(300):
        if name.startswith('switch'):
            b = pi / 2 * rng.random()
            p, mine = (b,), switch_src(int(name[6:]), b)
        elif name.startswith('face'):
            a = pi * rng.random(); b = pi * rng.random()
            if a + b > pi:
                continue
            p, mine = (a, b), None      # face handled separately
            continue
        else:
            a = pi * rng.random(); u = rng.random(); v = rng.random()
            if u * u + v * v - 2 * u * v * math.cos(a) < 0.014935663152905738:
                continue
            p, mine = (a, u, v), ring_src(int(name[4:]), a, u, v)
        if mine is None:
            continue
        mv = f([iv.mpf(x) for x in p])
        if mv is None:
            continue
        worst = max(worst, abs(float(mv.a) - mine))
    worst_all = max(worst_all, worst)
    print(f'{name:9s} {worst:18.3e}')
print('\noverall worst (switch+ring):', f'{worst_all:.3e}')
print('=> source-index formula matches the running bytecode'
      if worst_all < 1e-9 else '=> MISMATCH, formula still not right')
json.dump({'switch_ring_worst': worst_all},
          open(HERE / 'kernel_source_index_crosscheck.json', 'w'), indent=2)
