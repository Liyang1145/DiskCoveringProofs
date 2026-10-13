"""Does the line-91 clip (|dw/da| <= L = R/sqrt(1-R^2)) hold where the code actually evaluates it,
and if not, does the box enclosure nonetheless stay sound?

Two questions:
 Q1. max |dw/da| over the ADMISSIBLE set (q >= qmin, w <= pi/2, a in [0,pi], u,v in [0,1]).
 Q2. For boxes in the violating region, compare the module's ring closure interval with the
     true pointwise supremum inside that box (the property the branch-and-bound needs).
"""
import io, math, os, sys
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

R, R2 = 0.38, 0.38 ** 2
L = R / math.sqrt(1 - R2)
pi = math.pi
qmin = 4 * math.sin(pi - 8 * math.asin(R)) ** 2 / R2
fam = {n: f for n, f, d in ns['factors']}
print(f'L={L:.9f}  qmin={qmin:.9f}')


def admissible(a, u, v):
    q = u * u + v * v - 2 * u * v * math.cos(a)
    if q < qmin:
        return None
    if R * math.sqrt(q) / 2 > 1:
        return None
    return q


print('\n=== Q1: max |dw/da| = R^2 u v sin a / q over the admissible set ===')
mx = (0, None)
iv_best = {}
for ia in range(1, 3000):
    a = pi * ia / 3000
    sa, ca = math.sin(a), math.cos(a)
    for iu in range(1, 41):
        u = iu / 40
        for ivv in range(1, 41):
            v = ivv / 40
            q = u * u + v * v - 2 * u * v * ca
            if q < qmin:
                continue
            wa = R2 * u * v * sa / q
            if wa > mx[0]:
                mx = (wa, (a, u, v, q))
print(f'  max |dw/da| = {mx[0]:.6f} at (a,u,v,q)={tuple(round(x,6) for x in mx[1])}'
      f'   ratio to L = {mx[0]/L:.3f}')
print(f'  => clip at line 91 is {"VIOLATED" if mx[0] > L else "valid"} on the admissible set')

print('\n=== Q2: box enclosure in the violating region (module closure vs true sup) ===')
bad = []
for (ac, uc, vc, h) in [(0.50, 0.55, 0.55, 1e-3), (0.30, 0.55, 0.55, 1e-3),
                        (0.10, 0.55, 0.55, 1e-3), (0.10, 0.55, 0.55, 1e-2),
                        (0.05, 0.55, 0.55, 1e-3), (0.21, 0.95, 0.95, 1e-3),
                        (0.21, 0.95, 0.95, 1e-2), (0.05, 0.60, 0.50, 1e-2)]:
    box = [iv.mpf([ac - h, ac + h]), iv.mpf([uc - h, uc + h]), iv.mpf([vc - h, vc + h])]
    v = fam['ring0'](box)
    if v is None:
        print(f'  box ({ac},{uc},{vc},h={h}): rejected by qmin filter')
        continue
    top = float(v.b)
    tmax, argm = -1e9, None
    N = 25
    for i in range(N + 1):
        a = ac - h + 2 * h * i / N
        for j in range(N + 1):
            u = uc - h + 2 * h * j / N
            for k in range(N + 1):
                vv = vc - h + 2 * h * k / N
                if admissible(a, u, vv) is None:
                    continue
                pv = fam['ring0']([iv.mpf(a), iv.mpf(u), iv.mpf(vv)])
                if pv is not None and float(pv.a) > tmax:
                    tmax, argm = float(pv.a), (a, u, vv)
    ok = top >= tmax - 1e-12
    print(f'  box a={ac} u={uc} v={vc} h={h}: interval upper={top:+.9f}  true sup={tmax:+.9f}  '
          f'{"OK" if ok else "*** ENCLOSURE VIOLATED ***"}')
    if not ok:
        bad.append((ac, uc, vc, h, top, tmax, argm))
print('  violations:', bad if bad else 'none')
