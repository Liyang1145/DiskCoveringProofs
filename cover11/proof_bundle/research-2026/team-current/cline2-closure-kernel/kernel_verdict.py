"""DECISIVE kernel verdict (module's own closures) + quantified impact + sound re-run.

Part A: scalar_quad/quad (lead/certify_q0_closure.py lines 21-32) do not enclose
        min_{x in [0,1]} (a x^2 + b x).  Concrete scalar counterexamples.
Part B: consequence measured with the MODULE'S OWN closure functions (no reconstruction):
        attained values exceed the certificate's per-family upper bounds.
Part C: sound replacement of the helper + B&B re-run of all 29 families, and the resulting
        total compared with pi.
"""
import io, json, math, os, sys, heapq, time
from contextlib import redirect_stdout
from pathlib import Path
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

interval, quad, scalar_quad = ns['interval'], ns['quad'], ns['scalar_quad']
pi = math.pi
cert = json.loads((LEAD / 'q0_closure_dual_certificate_0_3.json').read_text())
stored = {f['factor']: f['upper'] for f in cert['factors']}

print('=' * 78)
print('A. scalar_quad / quad do not enclose min_{x in [0,1]}(a x^2 + b x)')
print('=' * 78)
for a, b in [(0.5, -0.9), (0.25, -0.24), (1.0, -1.5), (0.493277789, -0.419664498)]:
    got = scalar_quad(iv.mpf(a), iv.mpf(b))
    xstar = -b / (2 * a)
    vall = a * xstar * xstar + b * xstar
    print(f'  a={a:+.9f} b={b:+.9f}: code=[{float(got.a):+.12f},{float(got.b):+.12f}]  '
          f'true min={vall:+.12f} at x*={xstar:.6f}  encloses? {float(got.a) <= vall <= float(got.b)}')
print('  mechanism: line 24 `if b.b<=0: return zero` fires whenever the linear coefficient')
print('  is (partly) negative, dropping the negative dip of the quadratic.')

print()
print('=' * 78)
print("B. consequence using the MODULE'S OWN closures")
print('=' * 78)
fam = {n: f for n, f, d in ns['factors']}
doms = {n: d for n, f, d in ns['factors']}


def grid_points(name):
    if name.startswith('switch'):
        return [(pi / 2 * k / 4000,) for k in range(4001)]
    if name.startswith('face'):
        return [(pi * i / 80, pi * j / 80) for i in range(81) for j in range(81 - i)]
    pts = []
    for ka in range(0, 41):
        for ku in range(0, 21):
            for kv in range(0, 21):
                pts.append((pi * ka / 40, ku / 20, kv / 20))
    return pts


viol = []
for name, f in fam.items():
    mx, arg = -1e9, None
    for p in grid_points(name):
        v = f([iv.mpf(x) for x in p])
        if v is None:
            continue
        if float(v.a) > mx:
            mx, arg = float(v.a), p
    ok = mx <= stored[name] + 1e-12
    if not ok:
        viol.append(name)
    print(f'  {name:9s} module grid max={mx:+.9f} at {tuple(round(x,4) for x in arg)}  '
          f'certified upper={stored[name]:.9f}  {"OK" if ok else "*** CERTIFIED UPPER TOO SMALL ***"}')
print('  families whose certificate upper is below an attained value:', viol)

whole = fam['switch0']([interval(0.0, float(pi / 2))])
print(f'\n  switch0 whole-domain interval from the module: '
      f'[{float(whole.a):+.9f},{float(whole.b):+.9f}] ; final reported upper '
      f'{stored["switch0"]:.9f} ; refinement claim violated: {float(whole.b) > stored["switch0"]}')

print()
print('=' * 78)
print('C. sound replacement and re-run of the same B&B')
print('=' * 78)


def scal_lo(A, B):
    """a value <= min_{x in [0,1]}(A x^2 + B x)"""
    cands = [0.0]
    cands.append(min(0.0, float((A + B).b)))            # pessimistic x=1 term
    lo_ = math.nan
    hi_ = math.nan
    if A.a > 0:
        hi_ = -float(B.b) / (2 * A.a)
    if A.b > 0:
        lo_ = -float(B.a) / (2 * A.b)
    lo = 0.0 if math.isnan(lo_) else max(0.0, lo_)
    hi = 1.0 if math.isnan(hi_) else min(1.0, hi_)
    for x in (lo, max(lo, min(hi, 0.5 * (lo + hi))), hi):
        cands.append(float((A * x * x + B * x).a))
    return min(cands)


def s_quad(A, B):
    """sound enclosure of min_{x in [0,1]}(A x^2 + B x)"""
    lo = scal_lo(A, B)
    hi = max(0.0, float((A + B).b))
    if hi < lo:
        hi = lo
    return interval(lo, hi)


# quick soundness self-test of s_quad against dense sampling
import random
rng = random.Random(1)
bad = 0
for _ in range(4000):
    a1 = rng.uniform(-0.7, 0.5)
    A = interval(a1, a1 + rng.uniform(0.0, 0.5))
    b1 = rng.uniform(-1.2, 0.4)
    B = interval(b1, b1 + rng.uniform(0.0, 0.3))
    got = s_quad(A, B)
    tmin = min(float((A * (i / 400) * (i / 400) + B * (i / 400)).a) for i in range(401))
    if float(got.a) > tmin + 1e-9:
        bad += 1
print(f'  s_quad self-test: {bad}/4000 sampled violations')

ns2 = dict(ns)
ns2['__name__'] = 'iso2'
ns2['quad'] = s_quad
ns2['scalar_quad'] = s_quad
with redirect_stdout(io.StringIO()):
    exec(compile(PRE, 'iso2', 'exec'), ns2)
fam2 = [(n, f, d) for n, f, d in ns2['factors']]
zf = ns2['z']
total2 = ns2['pi'] * (sum(zf[:9]) + 2 * sum(zf[9:11]) + sum(zf[50:71]) - 2 * zf[71] - 2 * zf[72]) \
    + 2 * zf[72] * ns2['asin'](2 * ns2['R']) - ns2['pi'] * sum(zf[112:])
print('  constant part =', total2)

results = []
t0 = time.time()
for name, fun, domain in fam2:
    uid = 0
    heap = []
    lower = -1e100
    discarded = -1e100
    count = 0
    tol = 0.001

    def add(box, fun=fun, domain=domain):
        global uid, lower, count, discarded
        val = fun([interval(l, h) for l, h in box])
        count += 1
        if val is None:
            return
        mids = [(l + h) / 2 for l, h in box]
        pt = fun([iv.mpf(m) for m in mids])
        if pt is not None:
            lower = max(lower, ns2['lowerfloat'](pt))
        ub = ns2['upperfloat'](val)
        if ub >= lower:
            heapq.heappush(heap, (-ub, uid, box))
            uid += 1
        else:
            discarded = max(discarded, ub)

    add(domain)
    while heap and -heap[0][0] > lower + tol:
        neg, _, box = heapq.heappop(heap)
        if -neg < lower:
            discarded = max(discarded, -neg)
            continue
        k = max(range(len(box)), key=lambda k: (box[k][1] - box[k][0]) / (domain[k][1] - domain[k][0]))
        l, h = box[k]
        m = (l + h) / 2
        for pair in [(l, m), (m, h)]:
            new = box.copy()
            new[k] = pair
            add(new)
        if count > 400000:
            break
    ub = max(discarded, -heap[0][0] if heap else discarded)
    results.append((name, ub, lower, count))
    total2 += iv.mpf(ub)
    print(f'   {name:9s} sound upper={ub:+.9f}  certified={stored[name]:.9f}  '
          f'delta={ub - stored[name]:+.3e}  evals={count}  t={time.time()-t0:.1f}s', flush=True)

print()
print('  corrected total =', total2)
print('  corrected total < pi ?', total2.b < ns2['pi'].a)
json.dump({'certified_total': cert['upper'], 'corrected_total': str(total2),
           'pi': str(ns2['pi']),
           'factors': [{'family': n, 'sound_upper': u, 'certified': stored[n], 'evals': c}
                       for n, u, lo_, c in results],
           'families_below_attained_value': viol},
          open(HERE / 'kernel_verdict.json', 'w'), indent=2)
print('\nwrote kernel_verdict.json')
