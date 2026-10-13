"""cline2-coupled-factors f10c: exact test of the endpoint-copy identity u_k = v_k.

Parametrization: the nine switch polar angles theta_0..theta_8 (the switches are
unit-circle points).  Given theta_k, the site c_k must be at distance exactly r from both
P_{k-1} and P_k, so c_k = midpoint(P_{k-1},P_k) +- sqrt(r^2 - |P_{k-1}-P_k|^2/4) * n_k,
n_k normal to the chord.  Fixing the sign choice (the site lies inside the ring, so the
inward normal) determines c_k up to the angular parameter.  The remaining equations are
the SAME switch condition for the next site: |P_k - c_{k+1}| = r.  That is nine equations
in nine unknowns, solved by Newton.

Then u_k = |P_{k-1}-c_k|/r and v_k = |P_k-c_k|/r are computed with no reference to the
symmetry of the ambient circle center, which is exactly the quantity in question.
"""
import numpy as np, math, json
from pathlib import Path
P = Path(__file__).parent
OUT = P / 'out'
pi = math.pi
r = 0.38
rng = np.random.default_rng(5)


def build(theta):
    """theta -> sites (inward side), returns (c, ok)"""
    Pt = np.stack([np.cos(theta), np.sin(theta)], 1)
    c = np.zeros((9, 2))
    for k in range(9):
        A = Pt[(k-1) % 9]; B = Pt[k]
        m = (A+B)/2; d = B-A; L = np.linalg.norm(d)
        if L/2 >= r:
            return None, False
        n = np.array([-d[1], d[0]])/L
        h = math.sqrt(max(r*r-L*L/4, 0.0))
        # inward = the side closer to the origin (the ring center is inside the disk)
        c1 = m+h*n; c2 = m-h*n
        c[k] = c1 if np.linalg.norm(c1) < np.linalg.norm(c2) else c2
    return c, True


def F(theta):
    """residual: switch condition |P_k - c_{k+1}| = r for all k"""
    c, ok = build(theta)
    if not ok:
        return None
    Pt = np.stack([np.cos(theta), np.sin(theta)], 1)
    return np.array([np.linalg.norm(Pt[k]-c[(k+1) % 9])-r for k in range(9)]), c, Pt


# --- a genuine starting point: the SAVED object's switch angles ---
d = np.load(OUT/'realized.npz', allow_pickle=True)
PK = d['PK']
th0 = np.unwrap(np.arctan2(PK[:, 1], PK[:, 0]))
res = F(th0)
print('saved-object switch angles: max residual of the switch equations =',
      np.abs(res[0]).max())
uu0 = np.array([np.linalg.norm(PK[(k-1) % 9]-d['C'][int(d['slot_site'][k])])/float(d['Rc'])
                for k in range(9)])
vv0 = np.array([np.linalg.norm(PK[k]-d['C'][int(d['slot_site'][k])])/float(d['Rc'])
                for k in range(9)])
print('saved object: u =', np.round(uu0, 12))
print('saved object: v =', np.round(vv0, 12), '  max|u-v| =', np.abs(uu0-vv0).max())

# --- scan a family: perturb the switch angles and re-solve by Newton ---
def newton(th, itmax=60):
    for it in range(itmax):
        f = F(th)
        if f is None:
            return None
        fv = f[0]
        if np.abs(fv).max() < 1e-13:
            return th, f[1], f[2]
        J = np.zeros((9, 9))
        h = 1e-7
        for j in range(9):
            thp = th.copy(); thp[j] += h
            fp = F(thp)
            if fp is None:
                return None
            J[:, j] = (fp[0]-fv)/h
        try:
            step = np.linalg.solve(J, -fv)
        except np.linalg.LinAlgError:
            return None
        th = th+step
        if np.abs(step).max() > 0.5:
            return None
    return None


worst = 0.0; recs = []
ok_ct = 0
for trial in range(60):
    th = th0 + rng.normal(0, 1.5, 9)
    got = newton(th)
    if got is None:
        continue
    th, c, Pt = got
    W = np.diff(np.r_[th, th[0]+2*pi])
    if np.any(W <= 1e-6):
        continue
    uu = np.array([np.linalg.norm(Pt[(k-1) % 9]-c[k])/r for k in range(9)])
    vv = np.array([np.linalg.norm(Pt[k]-c[k])/r for k in range(9)])
    if np.any(uu > 1+1e-9) or np.any(vv > 1+1e-9):
        continue
    if abs(W.sum()-2*pi) > 1e-9:
        continue
    ok_ct += 1
    dv = float(np.abs(uu-vv).max())
    recs.append((ok_ct, dv, W.max(), W.min()))
    if dv > worst:
        worst = dv
    print(f'  #{ok_ct} max|u-v|={dv:.3e}  w in [{W.min():.4f},{W.max():.4f}]')
print(f'\nconverged genuine diagrams: {ok_ct}   worst max_k|u_k-v_k| = {worst:.3e}')
np.save(OUT/'uv_probe.npy', np.array(recs))
