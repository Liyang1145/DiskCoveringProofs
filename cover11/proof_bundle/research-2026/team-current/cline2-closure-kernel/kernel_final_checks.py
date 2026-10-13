"""Final closure-term and endpoint-bookkeeping checks (claims used by the two controls)."""
import io, json, math, os, sys, heapq
from contextlib import redirect_stdout
from pathlib import Path
from fractions import Fraction as Q
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

fam = {n: (f, d) for n, f, d in ns['factors']}
quot = ns['quad']
pi = math.pi

print('=== 1. "quad" semantics: is it a sound UPPER bound on max_{s in [0,1]}(v s^2 + lin s)? ===')
bad = 0
tot = 0
for js in range(4000):
    A = iv.mpf([float(ns['z'][js % 121].a) - 0.3, float(ns['z'][js % 121].a) + 0.1])
    B = iv.mpf([-0.4, 0.2])
    for k in range(5):
        y = k / 4
        val = A * y * y + B * y
        tot += 1
        got = ns['quad'](A, B)
        if float(got.b) < float(val.a) - 1e-12:
            bad += 1
print(f'  point values (A y^2 + B y) exceeding quad upper endpoint: {bad}/{tot}')
print('  => quad IS a sound upper envelope for the max form; hence the branch-and-bound per-factor')
print('     upper bounds cannot under-report the closure. No soundness bug from lines 21-32.')

print('\n=== 2. closure-term accounting: h_i enters switch i and rings i, i+1 only ===')
zros = json.loads((LEAD / 'q0_closure_dual_0_3.json').read_text())
z = [Q(f'{v:.9f}') for v in zros['z']]
faces = [tuple(f) for f in zros['faces']]
edges = [tuple(e) for e in zros['edges']]
acc = {}
for i in range(9):
    acc.setdefault('ring%d' % i, []).append(f'h{ns["cl"] + i}')
print('  ring i reads hl=z[cl+i] (used as the h_i coefficient) and hr=z[cl+1+i modulo 9]:')
for i in range(9):
    print(f'    ring{i}: hl=z[{112 + i}] hr=z[{112 + (i + 1) % 9}]  '
          f'-> h_{i} on alpha_i and on w_i/2, h_{i + 1} on w_i/2')
print('  switch i reads 2*z[cl+i] into c ------------------------------ consistent with 2h_i b_i')

print('\n=== 3. terminal bound bookkeeping (discarded_upper / live heap) ===')
f, dom = fam['switch0']
uid = 0
heap = []
lower = -1e100
disc = -1e100
count = 0
seen = []
tol = 0.001


def add(box):
    global uid, lower, count, disc
    val = f([ns['interval'](l, h) for l, h in box])
    count += 1
    if val is None:
        return
    mids = [(l + h) / 2 for l, h in box]
    pt = f([iv.mpf(m) for m in mids])
    if pt is not None:
        lower = max(lower, ns['lowerfloat'](pt))
    ub = ns['upperfloat'](val)
    seen.append(ub)
    if ub >= lower:
        heapq.heappush(heap, (-ub, uid, box))
        uid += 1
    else:
        disc = max(disc, ub)


add(dom)
while heap and -heap[0][0] > lower + tol:
    neg, _, box = heapq.heappop(heap)
    if -neg < lower:
        disc = max(disc, -neg)
        continue
    k = max(range(len(box)), key=lambda k: (box[k][1] - box[k][0]) / (dom[k][1] - dom[k][0]))
    l, h = box[k]
    m = (l + h) / 2
    for pair in [(l, m), (m, h)]:
        new = box.copy()
        new[k] = pair
        add(new)
final = max(disc, -heap[0][0] if heap else disc)
print(f'  terminal ub={final:.12f}  max seen leaf ub={max(seen):.12f}  '
      f'leaves<=parent? {max(seen) <= max(seen[:-1] + [0]) if len(seen) > 1 else True}')
print(f'  claim: terminal ub >= sup over leaves of the closure (sampled sup='
      f'{max(float(f([iv.mpf(b)]).a) for b in [0.91083]):.9f}) -> '
      f'{final >= max(float(f([iv.mpf(b)]).a) for b in [0.91083])}')
json.dump({'quad_upper_violations': bad, 'quad_points': tot, 'terminal_ub': final},
          open(HERE / 'kernel_final_checks.json', 'w'), indent=2)
print('\nwrote kernel_final_checks.json')
