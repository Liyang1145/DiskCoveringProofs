"""calib.py -- (a) n12 calibration of my clean-room kernel vs published readings;
(b) cross-check of my kernel vs the OLD members/stress kernel on the n12 network.
Read-only on n12.
"""
import json, sys
from pathlib import Path
import numpy as np
import mpmath as mp

mp.mp.dps = 50
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[1] / "stress" / "py"))
import stress2
from stress2 import build_edges, all_dirs, A_matrix, taus, gaps_from_taus

ROOT = HERE.parents[4]
N12 = ROOT / "research-2026/n12-global"
OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

W("== calibration: n12 proven candidate ==")
cal = json.loads((N12 / "evidence/d3-chart-calibration.json").read_text(encoding="utf-8"))
a, t, r, w = [mp.mpf(s) for s in cal["root"]]
b = (1 + a + r) / 2
S = b * b + w * w / 3
X = {"x": -b * r * r / (S - b), "y": (b - 1) * S / (S - b), "p": mp.mpf(1), "q": 2 * (1 - b) / r}
X["u"] = X["q"] * r / (2 * a - t + r)
X["j"] = X["u"] * (2 * t - 2 * r - a) / r
X["z"] = X["j"] * r * t / (1 - t * t - r * r)
Wtot = 6 * X["x"] + 6 * X["y"] + 6 * X["z"] + 6 * X["p"] + 3 * X["q"] + 6 * X["u"] + 3 * X["j"]
W("(a) published n12 weights (from calib_n12.py, independent of my kernel):")
W("    normalised min weight = %.12f   (expected 0.01165992192009)" % float(min(X.values()) / Wtot))

ang = [2 * mp.atan2(w / mp.sqrt(3), b), 2 * mp.pi / 3 - 2 * mp.atan2(w / mp.sqrt(3), b), 2 * mp.pi / 3,
       2 * mp.pi / 3 + 2 * mp.atan2(w / mp.sqrt(3), b), 4 * mp.pi / 3 - 2 * mp.atan2(w / mp.sqrt(3), b),
       4 * mp.pi / 3, 4 * mp.pi / 3 + 2 * mp.atan2(w / mp.sqrt(3), b), 2 * mp.pi - 2 * mp.atan2(w / mp.sqrt(3), b), 2 * mp.pi]
anchors = [(mp.cos(x), mp.sin(x)) for x in ang[:8]] + [(mp.cos(ang[7]), mp.sin(ang[7]))]     # 9 distinct anchors (last entry 2pi duplicates 0)
rot = lambda th: [(mp.cos(th), -mp.sin(th)), (mp.sin(th), mp.cos(th))]
sites = []
for k in range(3):
    Rk = rot(2 * mp.pi * k / 3)
    mv = lambda M, p: (M[0][0] * p[0] + M[0][1] * p[1], M[1][0] * p[0] + M[1][1] * p[1])
    sites.append(mv(Rk, (b, w / mp.sqrt(3))))
    sites.append(mv(rot(2 * mp.pi * k / 3 + mp.pi / 3), (t, 0)))
    sites.append(mv(rot(2 * mp.pi * (k + 1) / 3), (b, -w / mp.sqrt(3))))
hubs = [(mp.cos(2 * mp.pi * k / 3) * a, mp.sin(2 * mp.pi * k / 3) * a) for k in range(3)]
sites = sites + hubs
wits = [(mp.cos(2 * mp.pi * k / 3) * (a + r), mp.sin(2 * mp.pi * k / 3) * (a + r)) for k in range(3)] + \
       [(mp.cos(2 * mp.pi * k / 3 + mp.pi / 3) * (t - r), mp.sin(2 * mp.pi * k / 3 + mp.pi / 3) * (t - r)) for k in range(3)]
faces = [(8, 0, 9), (2, 3, 10), (5, 6, 11), (9, 10, 1), (10, 11, 4), (11, 9, 7)]
owners = [(i, (i + 1) % 9) for i in range(9)]
E = build_edges(anchors, sites, wits, faces, owners)
dirs = all_dirs(anchors, sites, wits, E)
A = A_matrix(anchors, sites, wits, E, dirs)
W("")
W("(b) my kernel on the n12 network: anchors=%d sites=%d witnesses=%d edges=%d ; rank(A)=%d"
  % (len(anchors), len(sites), len(wits), len(E), np.linalg.matrix_rank(A)))

# stress cone: min sum alpha s.t. A alpha = 0, alpha>=0, sum=1
from scipy.optimize import linprog
m, n = A.shape
c = np.ones(n)
res = linprog(c, A_eq=np.vstack([A, np.ones(n)]), b_eq=np.hstack([np.zeros(m), 1.0]),
              bounds=[(0, None)] * n, method="highs")
W("    LP status=%s ; min sum alpha (unconstrained cone) = %.12e" % (res.status, res.fun if res.fun is not None else -1))
if res.success:
    alpha0 = np.array(res.x)
    if alpha0.sum() > 1e-12:
        W("    -> cone nonempty, normalized min weight = %.12f" % (alpha0.min() / alpha0.sum()))
        # exact verify in mp
        Am = [[mp.mpf(float(A[i, j])) for j in range(n)] for i in range(m)]
        am = [mp.mpf(float(x)) for x in alpha0]
        eq = [sum(Am[i][j] * am[j] for j in range(n)) for i in range(m)]
        W("    corrected: max |A alpha| = %.3e (normalized alpha)" % float(max(abs(v) for v in eq) / sum(am)))
    else:
        W("    -> cone EMPTY (only trivial nonneg solution)")

# Schur complement + M for the n12 reading 6.684002e-05 / 2.366154692e-03
def schur_and_M(anchors, sites, wits, E, alpha, U12, na):
    """weighted Laplacian with all nodes; eliminate free nodes (sites+witnesses) in order;
    returns anchor-block Schur q, M, eig on 1^perp"""
    Z = list(anchors) + list(sites) + list(wits)
    nn = len(Z)
    L = [[mp.mpf(0)] * nn for _ in range(nn)]
    for e, (u, v) in enumerate(E):
        wv = mp.mpf(float(alpha[e]))
        L[u][u] += wv; L[v][v] += wv; L[u][v] -= wv; L[v][u] -= wv
    order = list(range(na, nn))
    for ii, k in enumerate(order):
        p = L[k][k]
        assert p > 0, ("pivot", k, p)
        rem = order[ii + 1:] + list(range(na))
        for ix_i, i in enumerate(rem):
            if L[i][k] == 0:
                continue
            for j in rem[ix_i:]:
                val = L[i][j] - L[i][k] * L[k][j] / p
                L[i][j] = val
                if j != i:
                    L[j][i] = val
    q = {}
    for i in range(na):
        for j in range(i + 1, na):
            q[i, j] = -L[i][j]
    # M with c_d = T_d(1-2U^2) exact rational
    from fractions import Fraction as F
    U = F(U12)
    c1 = 1 - 2 * U * U
    cd = {1: c1}
    prev, cur = F(1), c1
    for d in range(2, 5):
        nxt = 2 * c1 * cur - prev
        cd[d] = nxt; prev, cur = cur, nxt
    lab = lambda i, j: min(abs(i - j), na - abs(i - j))
    M = [[mp.mpf(0)] * na for _ in range(na)]
    for (i, j), qq in q.items():
        d = lab(i, j)
        c = cd.get(d)
        if c is None:
            continue
        vv = 2 * qq * mp.mpf(c.numerator) / mp.mpf(c.denominator)
        M[i][i] += vv; M[j][j] += vv; M[i][j] -= vv; M[j][i] -= vv
    G = mp.matrix(na - 1, na - 1)
    for k in range(1, na):
        for l in range(1, na):
            G[k - 1, l - 1] = M[0][0] - M[0][l] - M[k][0] + M[k][l]
    ev = mp.eigsy(G, eigvals_only=True)
    return q, M, [float(v) for v in ev]

q, M, ev1 = schur_and_M(anchors, sites, wits, E, alpha0, "0.361102963744508672616920293904", len(anchors))
W("")
W("(c) my Schur/M on n12: min Schur conductance = %.12e (expected 6.68400214e-05)" % min(float(v) for v in q.values()))
W("    M on 1^perp min eigenvalue = %.12e (expected 2.3661546922e-03)" % ev1[0])

# (d) cross-check with the OLD members/stress kernel (import)
W("")
W("(d) cross-check vs OLD members/stress/py/stress_core.py on the same network:")
try:
    from stress_core import Net
    net = Net(anchors, sites, faces)
    net.add_anchor_edges([tuple(ss) for ss in owners])
    net.add_face_edges(wits)
    alpha_old, tmax = net.positive_stress()
    W("    OLD kernel: edges=%d t_max=%.10f min alpha=%.10f sum=%.12f" % (len(net.edges), tmax, alpha_old.min(), alpha_old.sum()))
    qold = net.schur(alpha_old)
    W("    OLD kernel: min Schur = %.12e" % min(qold.values()))
    W("    my alpha vs old alpha (normalized): max abs diff = %.3e" % float(np.abs(alpha0 / alpha0.sum() - alpha_old / alpha_old.sum()).max()))
except Exception as ex:
    W("    (old kernel import failed: %s)" % ex)

(HERE.parent / "logs/calib.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/calib.txt")

