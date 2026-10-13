"""Find the exact unsound interval step.

Facts to explain:
  * module switch0 closure value at b=0 is +0.019460...  (fine-point box agrees)
  * the same factor's B&B reports upper = 0.0009836057
Therefore some interval evaluation must return an upper endpoint below an in-box point value.
This script searches for such pairs and prints the offending operation.
"""
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
interval, quad, scalar_quad, upperfloat = ns['interval'], ns['quad'], ns['scalar_quad'], ns['upperfloat']
pi = math.pi
R2 = (19 / 50) ** 2

print('=== switch0: closure value vs interval enclosure on nested boxes ===')
f, dom = fam['switch0']
for (lo_, hi_) in [(0.0, pi / 2), (0.0, 1e-9), (0.0, 0.0), (0.0, 1e-6), (0.01, 0.02),
                   (pi / 4, pi / 4), (1.5, 1.5707963267948966)]:
    box = [interval(lo_, hi_)]
    v = f(box)
    print(f'  box=[{lo_!r},{hi_!r}] -> {v}   (upper={float(v.b):+.12f})')
    # true corner values
    for b in {lo_, hi_}:
        pv = f([iv.mpf(b)])
        print(f'      point b={b!r}: {pv}  (a={float(pv.a):+.12f}, upper={float(pv.b):+.12f})')

print('\n=== the closed-form corner value versus the interval top ===')
caps = [float(v.a) for v in f.__defaults__]
c, d, e, g, h = caps
for b in (0.0, pi / 2):
    val = c * b + min(0.0, (R2 * math.sin(2 * b) / 2 - d * math.sin(b) ** 2 + e) + (g * math.sin(b) + h))
    print(f'  b={b:.9f}: closed form = {val:+.12f}')

print('\n=== brute search: boxes whose interval top is below an inside point value ===')
bad = []
rng = __import__('random').Random(11)
for it in range(4000):
    lo_ = (pi / 2) * rng.random() ** 2
    hi_ = min(pi / 2, lo_ + 10 ** rng.uniform(-9, -1))
    v = f([interval(lo_, hi_)])
    if v is None:
        continue
    top = float(v.b)
    for t in (lo_, hi_, 0.5 * (lo_ + hi_)):
        pv = f([iv.mpf(t)])
        if pv is not None and float(pv.a) > top + 1e-15:
            bad.append((lo_, hi_, t, top, float(pv.a), str(v)))
            break
    if len(bad) >= 5:
        break
print(f'found {len(bad)} counterexamples (interval top < inside point value):')
for b in bad:
    print(f'  box=[{b[0]:.9f},{b[1]:.9f}] top={b[3]:+.12f}  point {b[2]:.9f} has value {b[4]:+.12f}')
    print(f'     interval was {b[5]}')

print('\n=== quad() sanity on the exact switch integrand ===')
for b in (0.0, 0.5, pi / 2):
    bb = iv.mpf(b)
    vv = R2 * iv.sin(2 * bb) / 2 + 0.24426813 * iv.sin(bb) ** 2 + 0.249009659
    lv = -0.170654839 * iv.sin(bb) - 0.249009659
    q = quad(vv, lv)
    print(f'  b={b:.6f}: quad({float(vv.a):+.9f},{float(lv.a):+.9f}) = {q}  '
          f'true min(0,V+lin) = {min(0.0, float(vv.a) + float(lv.a)):+.9f}')
    for x in (0.0, 0.5, 1.0):
        val = float(vv.a) * x * x + float(lv.a) * x
        print(f'      x={x}: integrand={val:+.12f} inside {q}? '
              f'{float(q.a) - 1e-15 <= val <= float(q.b) + 1e-15}')
