"""DECISIVE minimal audit: per-factor certified upper vs the true supremum of the module's own
closure evaluated pointwise (radial variable sampled in the real box [0,1], not interval-boxed).

This tests the only soundness property the certificate needs:
    for every factor,  sup_{x in domain} (closure value)  <=  certified upper.
The factor is linear in the z coefficients and the closure is exactly the code's own bytecode.
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
cert = json.loads((LEAD / 'q0_closure_dual_certificate_0_3.json').read_text())
stored = {f['factor']: f['upper'] for f in cert['factors']}
pi = math.pi

print('per-family: pointwise max of the module closure over its own domain')
print(f'{"family":9s} {"pointwise max":>16s} {"argmax":>28s} {"certified":>12s}   verdict')
viol = []
worst_margin = {}
for name, f in fam.items():
    mx, am = -1e9, None
    if name.startswith('switch'):
        for k in range(20001):
            b = pi / 2 * k / 20000
            v = f([iv.mpf(b)])
            if v is not None and float(v.a) > mx:
                mx, am = float(v.a), (b,)
    elif name.startswith('ring'):
        for ka in range(0, 61):
            a = pi * ka / 60
            for ku in range(0, 21):
                for kv in range(0, 21):
                    p = (a, ku / 20, kv / 20)
                    v = f([iv.mpf(x) for x in p])
                    if v is not None and float(v.a) > mx:
                        mx, am = float(v.a), p
    else:                                  # face: radial box is 2-D, sample densely
        for i in range(0, 121):
            for j in range(0, 121 - i):
                p = (pi * i / 120, pi * j / 120)
                v = f([iv.mpf(x) for x in p])
                if v is not None and float(v.a) > mx:
                    mx, am = float(v.a), p
    ok = mx <= stored[name] + 1e-12
    if not ok:
        viol.append(name)
    print(f'{name:9s} {mx:+16.9f} {str(tuple(round(float(x),5) for x in am)):>28s} '
          f'{stored[name]:12.9f}   {"OK" if ok else "*** UPPER TOO SMALL ***"}')

print()
print('families where the certified upper is below a pointwise-attained value:', viol)
print('number of violating families:', len(viol))
json.dump({'violations': viol,
           'detail': {k: v for k, v in worst_margin.items()}},
          open(HERE / 'kernel_pointwise_check.json', 'w'), indent=2)
