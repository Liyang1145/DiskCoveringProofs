"""root-cc2: find the working box radius for the Krawczyk test (strict interval form)"""
import sys
from pathlib import Path
import mpmath as mp
from mpmath import iv
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import ivkernel as K
mp.mp.dps = 80
iv.dps = 80

def M(x):
    return (mp.mpf(x.a.a) + mp.mpf(x.b.b)) / 2

m = [mp.mpf('0.326818068949914'), mp.mpf('0.291941118964939'), mp.mpf('0.331732034276234')]
Phi_m = K.phi_intervals(K.iv_thin(m[0]), K.iv_thin(m[1]), K.iv_thin(m[2]))
Jmp = K.jacobian_intervals(K.iv_thin(m[0]), K.iv_thin(m[1]), K.iv_thin(m[2]))
Jp = mp.matrix(3, 3)
for r in range(3):
    for c in range(3):
        Jp[r, c] = M(Jmp[r][c])
Yinv = mp.inverse(Jp)
Y = [[K.iv_thin(Yinv[r, c]) for c in range(3)] for r in range(3)]

for ds in ('5e-6', '1e-6', '1e-7', '1e-8', '1e-9', '1e-10', '1e-12', '0'):
    delta = mp.mpf(ds)
    Mz = K.jacobian_intervals(K.iv_from(m[0]-delta, m[0]+delta),
                              K.iv_from(m[1]-delta, m[1]+delta),
                              K.iv_from(m[2]-delta, m[2]+delta))
    # strict interval computation of K(X)
    Kr = []
    for r in range(3):
        acc = K.iv_thin(0)
        for c in range(3):
            iy = (K.iv_thin(1) if r == c else K.iv_thin(0)) - sum(Y[r][t] * Mz[t][c] for t in range(3))
            acc = acc + iy * K.iv_from(-delta, delta)
        # m_r - Y_r . Phi(m)
        base = K.iv_thin(m[r])
        for c in range(3):
            base = base - Y[r][c] * Phi_m[c]
        Kr.append(base + acc)
    margins = []
    for r in range(3):
        margins.append(min((m[r]-delta) - K.L(Kr[r]), K.R(Kr[r]) - (m[r]+delta)) * (-1))
    # margins[r] > 0 means containment
    ok = all(x > 0 for x in margins)
    print('delta=%-8s  radii=%s  margins=%s  %s'
          % (ds, [mp.nstr(K.wid(Kr[r])/2, 3) for r in range(3)],
             [mp.nstr(x, 3) for x in margins], 'PASS' if ok else 'fail'))
