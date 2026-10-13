"""Black-box ground truth for the module's per-factor closures.

For every switch index we tabulate the module closure over b in [0,pi/2] and compare with the
formula built from the closure's OWN captured coefficients (order-independent: we identify them
by algebraic value, not by variable name). Same for the ring families on a coarse grid.

This decides whether each per-factor bound in the certificate is sound, independent of my
reconstruction of the intended geometry.
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


def mod_val(f, box):
    v = f([iv.mpf(x) for x in box])
    return None if v is None else (float(v.a), float(v.b))


print('=== switch closures: module black-box vs captured-coefficient formula ===')
print(f'{"bi":>2} {"f(0)":>12} {"f(pi/4)":>12} {"f(pi/2)":>12}   formula (c,b0,e,g,h) built from captures')
rows = []
for bi in range(9):
    f = fam[f'switch{bi}']
    caps = [float(v.a) for v in f.__defaults__]     # 5 numbers, order unknown
    v0 = mod_val(f, [0.0]); v4 = mod_val(f, [pi / 4]); vh = mod_val(f, [pi / 2])
    # identify: f(0) = min(0, e + h) since sin0=0 -> r2 term = e, lin = h
    # f(pi/2): v = R2*sin(pi)/2 - d*1 + e = e - d ; lin = g + h
    best = None
    import itertools
    for perm in itertools.permutations(range(5)):
        c, d, e, g, h = (caps[p] for p in perm)
        f0 = min(0.0, e + h)
        f4 = None
        fh2 = c * (pi / 2) + min(0.0, (e - d) + (g + h))
        if abs(f0 - v0[0]) < 1e-9 and abs(fh2 - vh[0]) < 1e-9:
            best = (c, d, e, g, h)
            break
    rows.append((bi, v0, v4, vh, best))
    print(f'{bi:>2} {v0[0]:12.9f} {v4[0]:12.9f} {vh[0]:12.9f}   {best}')
    if best is None:
        print('      ^ no permutation of captured coefficients reproduces the module values!')

print('\n=== consistency of the module with its own B&B lower bound ===')
cert = json.loads((LEAD / 'q0_closure_dual_certificate_0_3.json').read_text())
stored = {f['factor']: f for f in cert['factors']}
for bi in range(9):
    f = fam[f'switch{bi}']
    v0 = mod_val(f, [0.0]); vh = mod_val(f, [pi / 2])
    s = stored[f'switch{bi}']
    print(f'  switch{bi}: module f(0)={v0[0]:+.9f} f(pi/2)={vh[0]:+.9f} | certificate upper={s["upper"]:.9f} '
          f'lower={s["lower"]:.9f} | upper>=f(pi/2)? {s["upper"] >= vh[0]} upper>=f(0)? {s["upper"] >= v0[0]}')

print('\n=== ring closures: coarse grid, module only ===')
for i in range(9):
    f = fam[f'ring{i}']
    worst = (1e9, None)
    for ka in range(24):
        a = pi * ka / 23
        for ku in range(7):
            u = ku / 6
            for kv in range(7):
                v = kv / 6
                if u * u + v * v - 2 * u * v * math.cos(a) < 0.014935663152905738:
                    continue
                res = mod_val(f, [a, u, v])
                if res is not None and res[0] < worst[0]:
                    worst = (res[0], (a, u, v))
    s = stored[f'ring{i}']
    print(f'  ring{i}: module grid min={worst[0]:+.9f} at {tuple(round(x,5) for x in worst[1])} | '
          f'cert upper={s["upper"]:.9f} lower={s["lower"]:.9f} | sound? {s["upper"] >= worst[0]}')
