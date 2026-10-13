"""root-cc2: debug of the Krawczyk containment gap"""
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

delta = mp.mpf('5e-6')
m = [mp.mpf('0.326818068949914'), mp.mpf('0.291941118964939'), mp.mpf('0.331732034276234')]
Phi_m = K.phi_intervals(K.iv_thin(m[0]), K.iv_thin(m[1]), K.iv_thin(m[2]))
Jmp = K.jacobian_intervals(K.iv_thin(m[0]), K.iv_thin(m[1]), K.iv_thin(m[2]))
Jp = mp.matrix(3, 3)
for r in range(3):
    for c in range(3):
        Jp[r, c] = M(Jmp[r][c])
Yinv = mp.inverse(Jp)
Y = [[K.iv_thin(Yinv[r, c]) for c in range(3)] for r in range(3)]
Mz = K.jacobian_intervals(K.iv_from(m[0]-delta, m[0]+delta),
                          K.iv_from(m[1]-delta, m[1]+delta),
                          K.iv_from(m[2]-delta, m[2]+delta))
YPhi = []
for r in range(3):
    acc = K.iv_thin(0)
    for c in range(3):
        acc = acc + Y[r][c] * Phi_m[c]
    YPhi.append(acc)
print('YPhi intervals:', [(mp.nstr(K.L(v), 20), mp.nstr(K.R(v), 20), mp.nstr(K.wid(v), 6)) for v in YPhi])
IY = [[None]*3 for _ in range(3)]
for r in range(3):
    for c in range(3):
        acc = K.iv_thin(0)
        for t in range(3):
            acc = acc + Y[r][t] * Mz[t][c]
        IY[r][c] = (K.iv_thin(1) if r == c else K.iv_thin(0)) - acc
print('I - Y M entries (lo, hi):')
for r in range(3):
    print('   ', [(mp.nstr(K.L(IY[r][c]), 8), mp.nstr(K.R(IY[r][c]), 8)) for c in range(3)])
print()
for r in range(3):
    acc = K.iv_thin(0)
    for c in range(3):
        acc = acc + IY[r][c] * K.iv_from(-delta, delta)
    t1lo = m[r] - K.R(YPhi[r])
    t1hi = m[r] - K.L(YPhi[r])
    print('row %d: m-YPhi(m)=[%s, %s]  (I-YM)(X-m)=[%s, %s]'
          % (r, mp.nstr(t1lo, 24), mp.nstr(t1hi, 24), mp.nstr(K.L(acc), 24), mp.nstr(K.R(acc), 24)))
    print('        K=[%s, %s]  X=[%s, %s]  margins=[%s, %s]'
          % (mp.nstr(t1lo + K.L(acc), 24), mp.nstr(t1hi + K.R(acc), 24),
             mp.nstr(m[r]-delta, 24), mp.nstr(m[r]+delta, 24),
             mp.nstr((t1lo + K.L(acc)) - (m[r]-delta), 6),
             mp.nstr((t1hi + K.R(acc)) - (m[r]+delta), 6)))
