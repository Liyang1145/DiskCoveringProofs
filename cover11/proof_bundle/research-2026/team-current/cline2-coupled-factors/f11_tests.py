"""cline2-coupled-factors f11: is u_k = v_k an identity, and does the first moment help?

TEST 1 (u=v): take a chart of genuine diagrams in the SWITCH-ANGLE parametrization.
theta_k are the switch polar angles; the site c_k sits at distance r from both P_{k-1}
and P_k (two-point locus), and the switch conditions for the complementary rings are
checked as residuals.  We report max_k |u_k - v_k| and the switch-condition residuals
side by side: if |u-v| is proportional to the residual, u=v is NOT an identity but only
holds on the exact solution manifold (and cannot be used as a free dual row).

TEST 2 (first moment): d/d(eps) of the feasible-dual bound when the first-moment
multipliers are switched on with size eps, on the lead's own feasible z0.
"""
import numpy as np, math, json, sys
from pathlib import Path
from scipy.optimize import linprog
P = Path(__file__).parent
OUT = P / 'out'
pi = math.pi
r = 0.38
rng = np.random.default_rng(17)

# ---------------- TEST 1 ----------------
d = np.load(OUT/'realized.npz', allow_pickle=True)
PK = d['PK']; C = d['C']; slot = [int(s) for s in d['slot_site']]
csave = np.array([C[s] for s in slot])
th_save = np.unwrap(np.arctan2(PK[:, 1], PK[:, 0]))


def sites_from_theta(th):
    Pt = np.stack([np.cos(th), np.sin(th)], 1)
    c = np.zeros((9, 2))
    for k in range(9):
        A = Pt[(k-1) % 9]; B = Pt[k]
        m = (A+B)/2; dd = B-A; L = np.linalg.norm(dd)
        if L/2 >= r:
            return None, None, None
        n = np.array([-dd[1], dd[0]])/L
        hh = math.sqrt(max(r*r-L*L/4, 0.0))
        c1 = m+hh*n; c2 = m-hh*n
        c[k] = c1 if np.linalg.norm(c1) < np.linalg.norm(c2) else c2
    return Pt, c, None


print('=== TEST 1: u_k - v_k under switch-angle perturbations ===')
print(f'{"eps":>8s} {"switchcond_resid":>18s} {"max|u-v|":>14s} {"wmax->2pi":>12s}')
for eps in [0.0, 1e-6, 1e-4, 1e-3, 1e-2]:
    pth = th_save + eps*np.sin(np.arange(9)*1.7)
    Pt, c, _ = sites_from_theta(pth)
    if Pt is None:
        print(f'{eps:8.0e}   (chart left the feasible range)'); continue
    sc = np.array([np.linalg.norm(Pt[k]-c[(k+1) % 9])-r for k in range(9)])
    W = np.diff(np.r_[pth, pth[0]+2*pi])
    uu = np.array([np.linalg.norm(Pt[(k-1) % 9]-c[k])/r for k in range(9)])
    vv = np.array([np.linalg.norm(Pt[k]-c[k])/r for k in range(9)])
    print(f'{eps:8.0e} {np.abs(sc).max():18.3e} {np.abs(uu-vv).max():14.3e} '
          f'{W.max():12.6f}')
print('saved object (exact): max|u-v| =',
      np.abs([np.linalg.norm(PK[(k-1) % 9]-csave[k])/float(d['Rc']) for k in range(9)] -
             [np.linalg.norm(PK[k]-csave[k])/float(d['Rc']) for k in range(9)]).max())

# ---------------- TEST 2 ----------------
sys.path.insert(0, str(P))
import f4_feasible_dual as F
print('\n=== TEST 2: does the first moment improve the bound? ===')
pr = F.build(open_L=True)
row = json.loads((F.LEAD/'q0_closure_dual_0_4.json').read_text())
z0 = np.concatenate([np.array(row['z']), np.zeros(21)])
bn = len(pr['factors'])
# bound as a function of a GLOBAL shift of the first-moment multipliers
print(f'{"eps":>10s} {"bound":>16s} {"delta vs eps=0":>16s}')
for eps in [0.0, 0.01, 0.05, 0.1, 0.2, 0.5]:
    z = z0.copy(); z[121:] = eps
    ub = float(pr['base'] @ z)
    for name, v, M in pr['factors']:
        ub += float(np.max(v + M @ z))
    print(f'{eps:10.3f} {ub:16.9f} {ub-3.175702557547944:16.3e}')
