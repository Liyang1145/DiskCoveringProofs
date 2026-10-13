"""Phase 4c: reduced gradient of R_shape along the TC family + verification of the TC KKT
statement at the certified root. Evaluation only (no optimization).

  * builds Phi: (a04, y0, y1, R) -> 42 angles (verified map, phase 4b)
  * g = grad_u R_shape(Phi(u)) at the root  ->  stationarity content in the 6 shape directions
  * TC system check: e_R vs sum_k lam_k grad_u f_k  (f = the lead's res5 contacts)
Writes only in r20-stress/out .
"""
import os, json, math
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from pathlib import Path
import numpy as np
import mpmath as mp

W_DIR = Path(__file__).parent; OUT = W_DIR / 'out'
LEAD = W_DIR.parent / 'lead'
mp.mp.dps = 60

D = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())
root = [mp.mpf(s) for s in D['numeric_root']]
a04r, y0r, y1r, Rr, lamr = root[:4], root[4], root[5], root[6], root[7:]

zz = {'__file__': str(LEAD / 'check_angle_only.py')}
exec((LEAD / 'check_angle_only.py').read_text(encoding='utf-8').split("a=ns['x0'][:42]")[0], zz)
ns, shape = zz['ns'], zz['shape']
faces = [list(f) for f in ns['faces']]


def tc_geo(u):
    a04 = [mp.mpf(float(v)) for v in u[:4]]
    y0, y1, R = mp.mpf(float(u[4])), mp.mpf(float(u[5])), mp.mpf(float(u[6]))
    a4 = mp.pi - 2 * sum(a04)
    a = [a04[0], a04[1], a04[2], a04[3], a4, a04[3], a04[2], a04[1], a04[0]]
    rho = [mp.cos(a[k]) - mp.sqrt(R * R - mp.sin(a[k]) ** 2) for k in range(9)]
    th = [mp.mpf(0)] * 9
    for k in range(5, 9):
        th[k] = th[k - 1] + a[k - 1] + a[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (a[k] + a[k + 1])
    C = [(rho[k] * mp.cos(th[k]), rho[k] * mp.sin(th[k])) for k in range(9)]
    U = []
    for k in range(9):
        k2 = (k + 1) % 9
        U.append((C[k][0] + C[k2][0] - mp.cos(th[k] + a[k]), C[k][1] + C[k2][1] - mp.sin(th[k] + a[k])))
    m_, d_ = (y0 + y1) / 2, (y1 - y0) / 2
    h_ = mp.sqrt(R * R - d_ * d_)
    return a, C, [(y0, mp.mpf(0)), (y1, mp.mpf(0))], U, (m_, h_), R


def res5(u):
    a, C, hubs, U, waist, R = tc_geo(u)
    dist = lambda p, q: mp.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)
    out = []
    for (k, l) in [(1, 1), (2, 0), (3, 0), (8, 1)]:
        out.append(dist(U[k], hubs[l]) - R)
    out.append(dist(waist, C[6]) - R)
    return out


def angle_vector(u):
    a, C, hubs, U, waist, R = tc_geo(u)
    pts = {((6 - k) % 9): C[k] for k in range(9)}
    pts[9], pts[10] = hubs[0], hubs[1]
    ang = []
    for f in faces:
        for j in range(3):
            p = pts[f[j]]; q = pts[f[(j + 1) % 3]]; r = pts[f[(j + 2) % 3]]
            v1 = (q[0] - p[0], q[1] - p[1]); v2 = (r[0] - p[0], r[1] - p[1])
            ang.append(float(mp.atan2(abs(v1[0] * v2[1] - v1[1] * v2[0]), v1[0] * v2[0] + v1[1] * v2[1])))
    for s in range(9):
        i = (5 - s) % 9
        ang.append(float(mp.asin(mp.sqrt((C[i][0] - C[(i + 1) % 9][0]) ** 2 + (C[i][1] - C[(i + 1) % 9][1]) ** 2) / (2 * R))))
    return np.array(ang)


u0 = np.array([float(v) for v in root[:7]])
Rsh = lambda u: float(shape(angle_vector(u))[0])
hh = 1e-7
g = np.array([(Rsh(u0 + hh * np.eye(7)[k]) - Rsh(u0 - hh * np.eye(7)[k])) / (2 * hh) for k in range(7)])
print('== reduced gradient of R_shape along the TC family at the certified root')
print('   d/da0..a3 =', np.array2string(g[:4], precision=8))
print('   d/dy0,y1  =', np.array2string(g[4:6], precision=8))
print('   d/dR      = %.8f' % g[6])
print('   |grad on the 6 shape directions| = %.3e   (0 => TC family stationarity matches the model)' % np.linalg.norm(g[:6]))
# TC KKT statement check: e_R = sum lam_k grad_u f_k
hr = 1e-8
Jf = np.array([[float((res5(u0 + hr * np.eye(7)[k])[i] - res5(u0 - hr * np.eye(7)[k])[i]) / (2 * hr)) for k in range(7)]
               for i in range(5)])
lhs = Jf.T @ np.array([float(v) for v in lamr])
print('== TC system check: sum_k lam_k grad f_k   (should equal e_R = (0,...,0,1))')
print('   computed =', np.array2string(lhs, precision=8))
print('   residual vs e_R: |computed - e_R|inf = %.3e' % float(np.abs(lhs - np.array([0, 0, 0, 0, 0, 0, 1.0])).max()))
print('   multipliers lam (certified) =', [mp.nstr(v, 8) for v in lamr], ' (all negative => mu = -lam > 0 in the standard KKT sign)')
out = dict(scope='reduced gradient of R_shape along the TC family + TC KKT statement check; evaluation only',
           u0=u0.tolist(), grad_Rshape=g.tolist(), norm_grad_6_shape=float(np.linalg.norm(g[:6])),
           dRshape_dR=float(g[6]), lam=[float(v) for v in lamr], Jf=Jf.tolist(),
           TC_KKT_residual_inf=float(np.abs(lhs - np.array([0, 0, 0, 0, 0, 0, 1.0])).max()))
(OUT / 'phase4c_tc_reduced_gradient.json').write_text(json.dumps(out, indent=2))
print('[done] -> out/phase4c_tc_reduced_gradient.json')
