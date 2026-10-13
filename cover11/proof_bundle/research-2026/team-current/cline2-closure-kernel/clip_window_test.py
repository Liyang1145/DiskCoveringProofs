"""Targeted test of the line-91 derivative clip and of the box-level enclosure in the region
where the clip can fail.

Claim under test (lead CLOSURE-KERNEL-ANALYTIC-AUDIT.md): |w_a|,|w_u|,|w_v| <= R/sqrt(1-R^2) = L
on the admissible domain, so clipping the derivative intervals at [-L,L] is justified.

Admissible domain used by the kernel: alpha in [0,pi], u,v in [0,1], q >= qmin,
w = 2 asin(R sqrt(q)/2) in [0, pi/2]  (switch point inside the unit disk).
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

R = 0.38
R2 = R * R
L = R / math.sqrt(1 - R2)
qmin = 4 * math.sin(math.pi - 8 * math.asin(R)) ** 2 / R2
pi = math.pi
print(f'R={R}  L=R/sqrt(1-R^2)={L:.6f}  qmin={qmin:.6f}')

print('\n=== 1. is |w_a| <= L on the admissible domain?  (dense scan) ===')
worst_a = (0, None)
worst_u = (0, None)
for ia in range(1, 60):
    a = pi * ia / 60
    for iu in range(21):
        u = iu / 20
        for ivv in range(21):
            v = ivv / 20
            q = u * u + v * v - 2 * u * v * math.cos(a)
            if q < qmin or q <= 0:
                continue
            if R * math.sqrt(q) / 2 > 1:
                continue
            w = 2 * math.asin(R * math.sqrt(q) / 2)
            if w > pi / 2 + 1e-12:
                continue
            den = math.sqrt(q) * math.sqrt(1 - R2 * q / 4)
            wa = R * u * v * math.sin(a) / den
            wu = R * (u - v * math.cos(a)) / den
            wv = R * (v - u * math.cos(a)) / den
            if abs(wa) > worst_a[0]:
                worst_a = (abs(wa), (a, u, v, w, q))
            if max(abs(wu), abs(wv)) > worst_u[0]:
                worst_u = (max(abs(wu), abs(wv)), (a, u, v, w, q))
print(f'  max |w_a| on admissible set = {worst_a[0]:.6f} at (a,u,v,w,q)='
      f'{tuple(round(x, 6) for x in worst_a[1])}   ratio to L = {worst_a[0]/L:.3f}')
print(f'  max max(|w_u|,|w_v|)        = {worst_u[0]:.6f} at '
      f'{tuple(round(x, 6) for x in worst_u[1])}   ratio to L = {worst_u[0]/L:.3f}')

print('\n=== 2. box-level enclosure test in the clip-violating region ===')
print('    (code closure interval upper vs true pointwise max inside the box)')
fam = {n: f for n, f, d in ns['factors']}
f0 = fam['ring0']
bad = []
for (ac, uc, vc, h) in [(0.83, 1.0, 1.0, 1e-3), (0.83, 1.0, 1.0, 1e-2),
                        (0.4, 1.0, 1.0, 5e-2), (0.2, 1.0, 0.98, 5e-2),
                        (1.2, 1.0, 0.98, 5e-2), (1.2, 1.0, 0.98, 1e-2)]:
    box = [iv.mpf([ac - h, ac + h]), iv.mpf([uc - h, uc + h]), iv.mpf([vc - h, vc + h])]
    val = f0(box)
    if val is None:
        print(f'  box around ({ac},{uc},{vc}) h={h}: rejected (None)')
        continue
    top = float(val.b)
    # true max inside the box by dense sampling
    tmax = -1e9
    argm = None
    for i in range(21):
        a = ac - h + 2 * h * i / 20
        for j in range(21):
            u = uc - h + 2 * h * j / 20
            for k in range(21):
                v = vc - h + 2 * h * k / 20
                q = u * u + v * v - 2 * u * v * math.cos(a)
                if q < qmin:
                    continue
                pv = f0([iv.mpf(a), iv.mpf(u), iv.mpf(v)])
                if pv is not None and float(pv.a) > tmax:
                    tmax, argm = float(pv.a), (a, u, v)
    ok = top >= tmax - 1e-12
    print(f'  box ({ac},{uc},{vc}) h={h}: interval upper={top:+.9f}  true max={tmax:+.9f}  '
          f'{"OK" if ok else "*** ENCLOSURE VIOLATED ***"}')
    if not ok:
        bad.append((ac, uc, vc, h, top, tmax, argm))
print('  violations:', bad if bad else 'none')
json.dump({'max_wa_over_L': worst_a[0] / L, 'worst_wa': worst_a[1],
           'max_wuv_over_L': worst_u[0] / L, 'worst_wuv': worst_u[1],
           'box_violations': [list(map(str, b)) for b in bad]},
          open(HERE / 'clip_window_test.json', 'w'), indent=2)
print('\nwrote clip_window_test.json')
