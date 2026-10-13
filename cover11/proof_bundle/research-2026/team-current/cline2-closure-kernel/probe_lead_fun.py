"""Probe the lead's own factor closures (import does no file writes; we re-run its B&B
for one switch factor with stdout redirected into OUR directory, so the lead tree is untouched).

Purpose: find out why the certificate's stored switch uppers (~1e-3) are far below what an
independent reconstruction of the same formula gives, and re-check the final total assembly.
"""
import io, json, math, os, sys
from contextlib import redirect_stdout
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAD = HERE.parent / 'lead'
os.chdir(LEAD)                      # the module resolves its inputs relative to cwd
sys.path.insert(0, str(LEAD))
sys.argv = ['certify_q0_closure.py', '0', '3']   # row/span only; we do not call the B&B path

buf = io.StringIO()
with redirect_stdout(buf):
    import certify_q0_closure as C   # noqa: E402  (executes module body, no writes)

print('module imported; factors built =', len(C.factors))
print('module stdout (should be empty):', repr(buf.getvalue()[-200:]))

fam = {name: (fun, dom) for name, fun, dom in C.factors}
z = [float(v) for v in C.row['z']]
R2 = (19 / 50) ** 2

def at_point(fun, xs):
    return fun([C.iv.mpf(x) for x in xs])

# ---- 1. the lead's own switch functions at b=0 and b=pi/2 -----------------------------
print('\n--- lead switch factors at b=0 and b=pi/2 ---')
for bi in range(9):
    f, dom = fam[f'switch{bi}']
    v0 = at_point(f, [0.0])
    vh = at_point(f, [math.pi / 2])
    print(f'switch{bi}: f(0)={float(v0.a):+.9f}..{float(v0.b):+.9f}   '
          f'f(pi/2)={float(vh.a):+.9f}..{float(vh.b):+.9f}')

# ---- 2. my reconstruction of the same three coefficients ------------------------------
print('\n--- independent coefficient reconstruction (mine) ---')
faces = [tuple(f) for f in C.faces]
edges = [tuple(e) for e in C.edges]
for bi in range(9):
    i, j = bi, (bi + 1) % 9
    ei = edges.index(tuple(sorted((i, j))))
    c = z[i] + z[j] - z[50 + ei] + 2 * z[112 + bi]
    d = z[11 + ei]
    e = z[32 + 2 * i + 1] + z[32 + 2 * j]
    g = -z[73 + ei]
    h = z[94 + 2 * i + 1] + z[94 + 2 * j]
    print(f'switch{bi}: c={c:+.9f} d={d:+.9f} e={e:+.9f} g={g:+.9f} h={h:+.9f} '
          f'-> R(0)={e:+.9f} R(pi/2)={c * math.pi / 2 + min(0.0, R2 * 0 - d * 1 + e + g * 1 + h):+.9f}')

# ---- 3. re-run the lead's own B&B for switch0/switch3/switch5 only --------------------
print('\n--- replay of the lead B&B for selected switch factors (same code path) ---')
import heapq, time
for name in ['switch0', 'switch3', 'switch5']:
    fun, domain = fam[name]
    uid = 0
    heap = []
    lower = -1e100
    discarded = -1e100
    count = 0

    def add(box, fun=fun, domain=domain):
        global uid, lower, count, discarded
        val = fun([C.interval(l, h) for l, h in box])
        count += 1
        if val is None:
            return
        mids = [(l + h) / 2 for l, h in box]
        pt = fun([C.iv.mpf(m) for m in mids])
        if pt is not None:
            lower = max(lower, C.lowerfloat(pt))
        ub = C.upperfloat(val)
        if ub >= lower:
            heapq.heappush(heap, (-ub, uid, box))
            uid += 1
        else:
            discarded = max(discarded, ub)

    add(domain)
    while heap and -heap[0][0] > lower + 0.001:
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
        if count > 200000:
            raise RuntimeError('budget')
    ub = max(discarded, -heap[0][0] if heap else discarded)
    print(f'{name}: replay upper={ub:.12f} lower={lower:.12f} evals={count} '
          f'(certificate stored upper={[f["upper"] for f in C.__dict__.get("result", []) if f["factor"] == name] or "n/a"})')

# ---- 4. the assembled total, recomputed three ways ------------------------------------
print('\n--- total assembly cross-check ---')
zs = [C.iv.mpf(f'{v:.9f}') for v in C.row['z']]
coeff_part = sum(zs[:9]) + 2 * sum(zs[9:11]) + sum(zs[50:71]) - 2 * zs[71] - 2 * zs[72]
print('coeff_part (module z)      =', coeff_part)
print('pi*coeff_part              =', coeff_part * C.pi)
print('2*zeta*asin(2R)            =', 2 * zs[72] * (2 * C.iv.atan2(C.iv.mpf(19) / 50 * 2, C.iv.sqrt(1 - (C.iv.mpf(19) / 50 * 2) ** 2))))
print('-pi*sum(z[112:])           =', -C.pi * sum(zs[112:]))
stored = json.loads((LEAD / 'q0_closure_dual_certificate_0_3.json').read_text())
print('sum of stored factor uppers=', sum(f['upper'] for f in stored['factors']))
print('stored total upper         =', stored['upper'])
