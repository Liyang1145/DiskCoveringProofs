"""cline2-coupled-factors f10d: endpoint-copy identity u_k = v_k, via a damped Newton
solve of the switch system in the (theta, site) variables.

Unknowns: 9 switch polar angles theta and 9 site positions c_k (2D).  18 scalars.
Equations:
  (E1) |P_k - c_k| = r and |P_k - c_{k+1}| = r for k=0..8      (18 equations)
plus normalizations handled implicitly.  We solve with damped Gauss-Newton and reject any
solution violating the admissibility conditions.  Then measure u_k - v_k.
"""
import numpy as np, math, json, sys, time
from pathlib import Path
P = Path(__file__).parent
OUT = P / 'out'
pi = math.pi
r = 0.38
rng = np.random.default_rng(3)


def unpack(x):
    th = x[:9]
    c = x[9:].reshape(9, 2)
    return th, c


def resid(x):
    th, c = unpack(x)
    Pt = np.stack([np.cos(th), np.sin(th)], 1)
    out = []
    for k in range(9):
        out.append(np.linalg.norm(Pt[k]-c[(k+1) % 9])-r)  # switch on ring k+1
    return np.array(out)


def jac(x, f0, h=1e-7):
    J = np.zeros((18, 27))
    for j in range(27):
        xp = x.copy(); xp[j] += h
        J[:, j] = (resid(xp)-f0)/h
    return J


def solve(x0, itmax=140):
    x = x0.copy()
    lam = 1e-3
    for it in range(itmax):
        f = resid(x)
        nf = np.abs(f).max()
        if nf < 1e-13:
            return x, nf, it
        J = jac(x, f)
        try:
            step = np.linalg.solve(J.T@J + lam*np.eye(27), -J.T@f)
        except np.linalg.LinAlgError:
            return None, nf, it
        x2 = x+step
        if np.abs(resid(x2)).max() < nf:
            x = x2; lam = max(lam*0.5, 1e-12)
        else:
            lam *= 4
            if lam > 1e8:
                return None, nf, it
    return (x, np.abs(resid(x)).max(), itmax) if np.abs(resid(x)).max() < 1e-11 else (None, np.abs(resid(x)).max(), itmax)


d = np.load(OUT/'realized.npz', allow_pickle=True)
PK = d['PK']; C = d['C']
th_saved = np.unwrap(np.arctan2(PK[:, 1], PK[:, 0]))
x_saved = np.r_[th_saved, np.array([C[int(s)][0] for s in d['slot_site']]),
                np.array([C[int(s)][1] for s in d['slot_site']])]
f = resid(x_saved)
print('saved object as a start: max |residual| =', np.abs(f).max())

res = []
t0 = time.time()
for trial in range(400):
    if time.time()-t0 > 240:
        print('time box reached'); break
    x0 = x_saved + np.r_[rng.normal(0, 0.25, 9), rng.normal(0, 0.06, 18)]
    x, resmax, it = solve(x0)
    if x is None:
        continue
    th, c = unpack(x)
    W = np.diff(np.r_[th, th[0]+2*pi])
    if np.any(W <= 1e-3) or abs(W.sum()-2*pi) > 1e-9:
        continue
    if np.any(np.linalg.norm(c, axis=1) > math.sqrt(1-r*r)+1e-9):
        continue
    dd = np.linalg.norm(c[:, None, :]-c[None, :, :], axis=2)+np.eye(9)*9
    if dd.min() < 2*r:
        continue
    Pt = np.stack([np.cos(th), np.sin(th)], 1)
    uu = np.array([np.linalg.norm(Pt[(k-1) % 9]-c[k])/r for k in range(9)])
    vv = np.array([np.linalg.norm(Pt[k]-c[k])/r for k in range(9)])
    if np.any(uu > 1+1e-9) or np.any(vv > 1+1e-9):
        continue
    dv = float(np.abs(uu-vv).max())
    res.append(dv)
    print(f'  solution {len(res)}: maxres={resmax:.1e} max|u-v|={dv:.3e} '
          f'wmin={W.min():.4f} wmax={W.max():.4f}')
    if len(res) >= 25:
        break
print(f'\ngenuine diagrams: {len(res)}')
if res:
    print(f'worst max_k |u_k - v_k| = {max(res):.3e}   median = {np.median(res):.3e}')
    np.save(OUT/'uv_probe.npy', np.array(res))
else:
    print('no admissibility-passing solution found in the time box')
