"""farkas_check.py -- is the candidate a first-order local minimum of the candidate-graph
incidence system, and what are the zero entries of the (Farkas) stress?

At the candidate the 62 active incidences are tight.  A direction w (in the 70 coordinates:
14 sites, 16 witnesses, 10 anchor angles) with grad_e . w < 0 for EVERY active edge would
strictly shrink every active incidence, hence give a cover of strictly smaller radius (C1281
sufficiency with the same combinatorial graph and ordered anchors), i.e. a local improvement.

By Gordan's theorem exactly one of the following holds:
  (i)  exists w with grad_e . w < 0 for all e            => local improvement direction;
  (ii) exists c >= 0, c != 0 with sum_e c_e grad_e = 0    => no such direction (a "stress").
This script decides which, and reports the sign pattern / zero entries of the stress.
"""
import json, sys
from pathlib import Path
import numpy as np
import mpmath as mp

mp.mp.dps = 50
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

scout = json.loads((ROOT / "research-2026/next-cover-global/lead/root-scout.json").read_text(encoding="utf-8"),
                   parse_float=str)
z, c_, r = (mp.mpf(x) for x in scout["z_c_r"])
s_ = mp.sqrt(1 - r * r)
a_ = (s_ + z) / 2
b_ = r + mp.sqrt(r * r - (a_ - z) ** 2)
d_ = 1 - mp.sqrt(r * r - c_ * c_)
t_ = r + mp.sqrt(r * r - z * z)
C = []
for sy in (1, -1):
    for sx in (1, -1):
        C.append((sx * a_, sy * b_))
for sy in (1, -1):
    for sx in (1, -1):
        C.append((sx * c_, sy * d_))
C += [(s_, mp.mpf(0)), (-s_, mp.mpf(0)), (z, mp.mpf(0)), (-z, mp.mpf(0)), (mp.mpf(0), -t_), (mp.mpf(0), t_)]
SWdeg = ["19.37393668027073", "51.774419687402606", "90.0", "128.2255803125974",
         "160.62606331972927", "199.37393668027073", "231.7744196874026",
         "270.0", "308.2255803125974", "340.62606331972927"]
TH = [mp.mpf(x) * mp.pi / 180 for x in SWdeg]
AN = [(mp.cos(x), mp.sin(x)) for x in TH]
OWN = [[0, 8], [0, 4], [4, 5], [1, 5], [1, 9], [3, 9], [3, 7], [6, 7], [2, 6], [2, 8]]
FACES = [(0, 4, 13), (0, 8, 10), (0, 10, 13), (1, 5, 13), (1, 9, 11), (1, 11, 13),
         (2, 6, 12), (2, 8, 10), (2, 10, 12), (3, 7, 12), (3, 9, 11), (3, 11, 12),
         (10, 11, 12), (10, 11, 13), (4, 5, 13), (6, 7, 12)]

def circum(P):
    A = mp.matrix([[2 * (P[1][0] - P[0][0]), 2 * (P[1][1] - P[0][1])],
                   [2 * (P[2][0] - P[0][0]), 2 * (P[2][1] - P[0][1])]])
    bb = mp.matrix([P[1][0] ** 2 + P[1][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2,
                    P[2][0] ** 2 + P[2][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2])
    sol = mp.lu_solve(A, bb)
    return (sol[0], sol[1])
WF = [circum([C[i] for i in f]) for f in FACES]
dist = lambda p, q: mp.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)
EDGES = []
for ai, ss in enumerate(OWN):
    for sj in ss:
        EDGES.append(("anchor", sj, ai, dist(AN[ai], C[sj])))
for fi, tri in enumerate(FACES):
    for sj in tri:
        EDGES.append(("face", sj, fi, dist(WF[fi], C[sj])))
active = [i for i, e in enumerate(EDGES) if abs(e[3] - r) < mp.mpf("1e-12")]
inact = [i for i in range(len(EDGES)) if i not in active]
N = 70
sd = lambda j: 2 * j
wd = lambda f: 28 + 2 * f
ad = lambda ai: 60 + ai
J = np.zeros((len(active), N))
for row, ei in enumerate(active):
    kind, sj, other, L = EDGES[ei]
    p = C[sj]; q = AN[other] if kind == "anchor" else WF[other]
    u = np.array([float((p[0] - q[0]) / L), float((p[1] - q[1]) / L)])
    J[row, sd(sj):sd(sj) + 2] += u
    if kind == "anchor":
        A = AN[other]
        J[row, ad(other)] = float(np.dot(u, np.array([float(A[1]), float(-A[0])])))
    else:
        J[row, wd(other):wd(other) + 2] -= u

W("== first-order local minimality of the candidate graph incidence system ==")
W("active incidences: %d ; variables: %d (28 site + 32 witness + 10 anchor)" % (len(active), N))
sv = np.linalg.svd(J, compute_uv=False)
W("rank(J) = %d (of %d rows, %d cols) ; rank deficiency = %d" % (
    int((sv > 1e-11 * sv[0]).sum()), J.shape[0], N, J.shape[0] - int((sv > 1e-11 * sv[0]).sum())))
W("smallest singular values: %s" % [float(x) for x in sv[-4:]])

from scipy.optimize import linprog
n = len(active)
# (ii) nonnegative stress: sum c_e grad_e = 0, sum c_e = 1, c >= 0
Aeq = np.vstack([J.T, np.ones((1, n))])
beq = np.hstack([np.zeros(N), 1.0])
res = linprog(np.zeros(n), A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * n, method="highs")
W("")
W("nonnegative stress LP (sum c_e grad_e = 0, sum c_e = 1, c >= 0): status = %s" % res.status)
if res.status == 0:
    c = res.x
    W("   FEASIBLE -> 0 in conv{grad_e}: no direction strictly decreases every active incidence.")
    W("   support of the stress: %d of %d ; entries > 1e-12: %s" % (
        int((c > 1e-12).sum()), n, [active[i] for i in range(n) if c[i] > 1e-12]))
    W("   zero-stress (in this support) active edges: %s" % [active[i] for i in range(n) if c[i] <= 1e-12])
    # per-edge maximal stress (which edges can carry no weight at all)
    mx = np.zeros(n)
    for i in range(n):
        cc = np.zeros(n); cc[i] = -1.0
        rr = linprog(cc, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * n, method="highs")
        mx[i] = -rr.fun if rr.status == 0 else 0.0
    fz = [active[i] for i in range(n) if mx[i] <= 1e-11]
    W("   edges forced to zero weight in EVERY nonnegative stress: %d -> %s" % (len(fz), fz))
    W("   per-edge max weight: min=%.3e max=%.3e" % (mx.min(), mx.max()))
else:
    W("   INFEASIBLE -> 0 not in conv{grad_e}: there is a direction w with grad_e.w < 0 for all e")
    W("   => first-order strictly shrinking direction (potential local improvement). MUST be verified.")
# (i) the strictly shrinking direction as an LP: minimise s s.t. grad_e.w + s <= 0, |w|_inf <= 1
Aub = np.zeros((n, N + 1))
Aub[:, :N] = J
Aub[:, N] = -1.0
bub = np.zeros(n)
Aub2 = np.vstack([Aub, np.hstack([np.eye(N), np.zeros((N, 1))]), np.hstack([-np.eye(N), np.zeros((N, 1))])])
bub2 = np.hstack([bub, np.ones(N), np.ones(N)])
cold = np.zeros(N + 1); cold[N] = 1.0
r2 = linprog(cold, A_ub=Aub2, b_ub=bub2, bounds=[(None, None)] * (N + 1), method="highs")
W("")
W("min over |w|_inf<=1 of max_e grad_e.w : %s" % (
    ("%.6e" % r2.x[N] if r2.status == 0 else "n/a")))
W("   (negative => a strictly shrinking direction exists)")
json.dump(dict(rank=int((sv > 1e-11 * sv[0]).sum()), n_active=n, stress_feasible=(res.status == 0),
               max_min_grad=(float(r2.x[N]) if r2.status == 0 else None),
               active_edge_ids=active,
               stress=(list(map(float, res.x)) if res.status == 0 else None)),
          open(HERE.parent / "evidence/farkas_check.json", "w"), indent=1)
(HERE.parent / "logs/farkas_check.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/farkas_check.txt")

