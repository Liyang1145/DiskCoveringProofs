"""Confirm and quantify the scalar_quad/quad unsoundness, plus a sound replacement check.

Bug class (lead/certify_q0_closure.py, lines 21-32):
    scalar_quad(a,b) is supposed to enclose  min_{x in [0,1]} (a x^2 + b x) .
    At the negative vertex  x* = -b/(2a)  (requires a>0, (2a+b)<0) the code only injects
    peak = -b^2/(4a) into the lower endpoint when
        (2*a+b).b <= 0     i.e. (2 a_max + b_max) <= 0,
    which is the *wrong* condition: with interval a=[a.a,a.b] > 0 and b<0 the true condition
    is (2*a.a + b.b) < 0. When  a.a>0, b<0  and  2*a.b+b.b > 0 > 2*a.a+b.b  the negative
    minimum is silently dropped from the enclosure.
"""
import io, os, sys, math, random
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
iv.pi


def truth(a, b):
    """exact-ish min of a x^2 + b x on [0,1] for scalar a,b"""
    cands = [0.0, a + b]
    if a != 0:
        x = -b / (2 * a)
        if 0 <= x <= 1:
            cands.append(a * x * x + b * x)
    return min(cands)


print('=== scalar cases (point boxes) ===')
cases = [(0.36, -0.33), (0.493277789, -0.419664498), (0.5, -0.9), (0.25, -0.24), (1.0, -1.5)]
for a, b in cases:
    got = scalar_quad(iv.mpf(a), iv.mpf(b))
    tr = truth(a, b)
    print(f'  a={a:+.6f} b={b:+.6f}: scalar_quad={got}  true min={tr:+.9f}  '
          f'contains? {float(got.a) - 1e-15 <= tr <= float(got.b) + 1e-15}')

print('\n=== random interval cases: does quad() enclose min over x in [0,1]? ===')
rng = random.Random(5)
bad = 0
worst = None
for _ in range(200000):
    aa = rng.uniform(0.05, 1.5)
    bb = rng.uniform(-1.0, -0.05)
    A = interval(aa * 1.0, aa * 1.0)
    B = interval(bb * 1.0, bb * 1.0)
    got = quad(A, B)
    tr = truth(A.a, B.a)
    if not (float(got.a) - 1e-15 <= tr <= float(got.b) + 1e-15):
        bad += 1
        if worst is None:
            worst = (A, B, got, tr)
print(f'  violations: {bad}/200000')
if worst:
    print('  example:', worst[0], worst[1], '-> quad =', worst[2], ' true min =', f'{worst[3]:+.9f}')
    a, b = float(worst[0].a), float(worst[1].a)
    print(f'    vertex x* = {-b/(2*a):.6f} (inside [0,1]); code returned lower endpoint '
          f'{float(worst[2].a):+.9f} instead of {worst[3]:+.9f}')

print('\n=== branch-by-branch explanation on one failing point ===')
a, b = 0.365908612, -0.330825947
A, B = interval(a, a), interval(b, b)
print(f'  a={a}, b={b}: 2a+b = {2*a+b:+.9f}  (vertex in [0,1]: {0 <= -b/(2*a) <= 1})')
print(f'  code path: (2*a+b).a>=0 ? {(2*A+B).a >= 0} ->   (2*a+b).b<=0 ? {(2*A+B).b <= 0}')
print(f'  code returned {scalar_quad(A, B)}; truth = {truth(a,b):+.9f}')
print(f'  => because (2a+b).b = {float((2*A+B).b):+.9f} > 0 the peak term is skipped.')

print('\n=== does the same shape occur in the real factors? (integrand coefficients over boxes) ===')
# switch family: V(b) and lin(b) as in the code; check each B&B-style box for the failing pattern
pi = math.pi
R2 = (19 / 50) ** 2
zs = [float(v.a) for v in ns['z']]
faces = [tuple(f) for f in ns['faces']]
edges = [tuple(e) for e in ns['edges']]
hits = 0
tot = 0
for bi in range(9):
    i, j = bi, (bi + 1) % 9
    ei = edges.index(tuple(sorted((i, j))))
    c = zs[i] + zs[j] - zs[50 + ei] + 2 * zs[112 + bi]
    d = zs[11 + ei]
    e = zs[32 + 2 * i + 1] + zs[32 + 2 * j]
    g = -zs[73 + ei]
    h = zs[73 + 2 * i + 1] + zs[73 + 2 * j]
    # scan tiny boxes around the b where 2V+lin changes sign
    for k in range(0, 2000):
        lo_ = pi / 2 * k / 2000
        hi_ = pi / 2 * (k + 1) / 2000
        # crude interval of V and lin on the box
        Vl = R2 * min(math.sin(2 * lo_), math.sin(2 * hi_)) / 2 - d * max(math.sin(lo_), math.sin(hi_)) ** 2 + e
        Vh = R2 * max(math.sin(2 * lo_), math.sin(2 * hi_)) / 2 - d * min(math.sin(lo_), math.sin(hi_)) ** 2 + e
        L = g * min(math.sin(lo_), math.sin(hi_)) + h
        Lh = g * max(math.sin(lo_), math.sin(hi_)) + h
        tot += 1
        if Vl > 0 and (2 * Vh + Lh) > 0 > (2 * Vl + L) and L < 0:
            hits += 1
    print(f'  switch{bi}: params c={c:+.6f} d={d:+.6f} e={e:+.6f} g={g:+.6f} h={h:+.6f}')
print(f'  boxes matching the failure pattern: {hits} of {tot} (crude scan)')
