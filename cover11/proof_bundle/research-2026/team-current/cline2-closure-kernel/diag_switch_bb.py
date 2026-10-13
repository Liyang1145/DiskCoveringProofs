"""Tight diagnostic: the module's switch0 closure, its interval evaluation, and the B&B
mechanics, all on the same objects."""
import io, json, math, os, sys, heapq
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
interval, quad, upperfloat, lowerfloat = ns['interval'], ns['quad'], ns['upperfloat'], ns['lowerfloat']
R2 = (19 / 50) ** 2
pi = math.pi

for bi in (0, 1):
    f, dom = fam[f'switch{bi}']
    print(f'\n=== switch{bi}: domain={dom} ===')
    hi = dom[0][1]
    for b in (0.0, hi / 2, hi - 1e-9, hi):
        v = f([iv.mpf(b)])
        print(f'  point box [{b!r}]: {v}   (a={float(v.a):+.12f}, b={float(v.b):+.12f})')
    # interval over sub-boxes
    for lo_, hi_ in [(0, hi), (hi - 1e-3, hi), (hi - 1e-6, hi), (hi * 0.6, hi)]:
        v = f([interval(lo_, hi_)])
        print(f'  box [{lo_:.6f},{hi_:.6f}] -> {v}')

print('\n=== replayed B&B for switch0 with instrumentation ===')
f, dom = fam['switch0']
uid = 0
heap = []
lower = -1e100
discarded = -1e100
count = 0
tol = 0.001


def add(box):
    global uid, lower, count, discarded
    val = f([interval(l, h) for l, h in box])
    count += 1
    if val is None:
        return
    mids = [(l + h) / 2 for l, h in box]
    pt = f([iv.mpf(m) for m in mids])
    if pt is not None:
        lower = max(lower, lowerfloat(pt))
    ub = upperfloat(val)
    if ub >= lower:
        heapq.heappush(heap, (-ub, uid, box))
        uid += 1
    else:
        discarded = max(discarded, ub)


add(dom)
print('initial box eval ub =', -heap[0][0] if heap else None, 'lower =', lower)
while heap and -heap[0][0] > lower + tol:
    neg, _, box = heapq.heappop(heap)
    if -neg < lower:
        discarded = max(discarded, -neg)
        continue
    k = max(range(len(box)), key=lambda k: (box[k][1] - box[k][0]) / (dom[k][1] - dom[k][0]))
    l, h = box[k]
    m = (l + h) / 2
    for pair in [(l, m), (m, h)]:
        new = box.copy()
        new[k] = pair
        add(new)
    if count > 200000:
        print('BUDGET EXCEEDED at count', count)
        break
print(f'terminated: count={count} lower={lower:.12f} max-ub-in-heap={(-heap[0][0] if heap else None)} discarded_upper={discarded:.12f}')
print('upper bound taken =', max(discarded, -heap[0][0] if heap else discarded))
print('\nSanity: direct evaluation of the same closure at b=hi:',
      f([iv.mpf(dom[0][1])]))
print('So a sound upper bound for this family must be >= that value.')
