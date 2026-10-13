"""n14kkt.py -- n14 sharp-candidate stress + capped-simplex KKT at the NEW stationary root.

Geometry: coordinates given by Lead (lead/root-scout.json z,c,r), expanded with the Lead's own
algebraic chain; verified independently (logs/step1_geom.txt, step4_cover2.txt).

Network: 10 boundary anchors (arc endpoints), 14 sites (disk centres), 14 tight interior
witnesses (empty-circle vertices of the 14 tight faces), 62 edges.
Domain: gap variables, sharp radius r* (L*=2asin r*), cap-active gaps {4,9}.

KKT (min form): A alpha = 0, alpha >= 0, g_k = c (k interior), g_k <= c (k in {4,9}).
"""
import json, sys
from pathlib import Path
import numpy as np
import mpmath as mp

mp.mp.dps = 60
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom import new_geom, centers_from, dist, norm

g = new_geom()
C = centers_from(g)
r = g["r"]
L = 2 * mp.asin(r)
OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

# ---------------- anchors (arc endpoints do not exist: each active arc reaches S^1 and meets
# the neighbouring arc at the switch point, which is the anchor)
SWITCH = [mp.mpf(x) for x in ["19.37393668027073", "51.774419687402606", "90.0", "128.2255803125974",
                              "160.62606331972927", "199.37393668027073", "231.7744196874026",
                              "270.0", "308.2255803125974", "340.62606331972927"]]
anchors = [(mp.cos(a * mp.pi / 180), mp.sin(a * mp.pi / 180)) for a in SWITCH]
owners = [[0, 8], [0, 4], [4, 5], [1, 5], [1, 9], [3, 9], [3, 7], [6, 7], [2, 6], [2, 8]]

FACES = [(0, 4, 13), (0, 8, 10), (0, 10, 13), (1, 5, 13), (1, 9, 11), (1, 11, 13),
         (2, 6, 12), (2, 8, 10), (2, 10, 12), (3, 7, 12), (3, 9, 11), (3, 11, 12),
         (10, 11, 12), (10, 11, 13)]


def circum(P):
    A = mp.matrix([[2 * (P[1][0] - P[0][0]), 2 * (P[1][1] - P[0][1])],
                   [2 * (P[2][0] - P[0][0]), 2 * (P[2][1] - P[0][1])]])
    b = mp.matrix([P[1][0] ** 2 + P[1][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2,
                   P[2][0] ** 2 + P[2][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2])
    sol = mp.lu_solve(A, b)
    return (sol[0], sol[1])


WITS = [circum([C[i] for i in f]) for f in FACES]

W("== n14 KKT at NEW stationary root ==")
W("r* = %s ; L*=2asin r* = %s" % (mp.nstr(r, 30), mp.nstr(L, 25)))
W("14 tight witnesses; witness radius check:")
for k, (f, wv) in enumerate(zip(FACES, WITS)):
    ds = [dist(wv, C[s]) for s in f]
    mx = max(abs(d - r) for d in ds)
    W("   face %2d %-14s w=(%s,%s) max| |w-site| - r* | = %s  |w|=%s" % (
        k, str(f), mp.nstr(wv[0], 12), mp.nstr(wv[1], 12), mp.nstr(mx, 4), mp.nstr(norm(wv), 12)))

# ---------------- edges
na, ns, nw = len(anchors), len(C), len(WITS)
edges = []
for i, ss in enumerate(owners):
    for s in ss:
        edges.append((i, na + s))
for k, f in enumerate(FACES):
    for s in f:
        edges.append((na + ns + k, na + s))
Z = list(anchors) + list(C) + list(WITS)
ne = len(edges)
W("")
W("nodes: anchors=%d sites=%d witnesses=%d ; edges=%d (anchor-site %d, witness-site %d)"
  % (na, ns, nw, ne, 2 * na, 3 * nw))

# unit directions along each edge, oriented u -> v
dirs = []
for (u, v) in edges:
    dv = (Z[v][0] - Z[u][0], Z[v][1] - Z[u][1])
    n_ = mp.sqrt(dv[0] ** 2 + dv[1] ** 2)
    assert n_ > mp.mpf("1e-30"), ("degenerate edge", u, v, n_)
    dirs.append((dv[0] / n_, dv[1] / n_))
# edge lengths
lens = [mp.sqrt((Z[v][0] - Z[u][0]) ** 2 + (Z[v][1] - Z[u][1]) ** 2) for (u, v) in edges]
W("edge lengths: min=%s max=%s  (all equal r*? %s)" % (
    mp.nstr(min(lens), 18), mp.nstr(max(lens), 18), max(abs(x - r) for x in lens) < mp.mpf("1e-25")))

# ---------------- equilibrium matrix A (2*ns x ne)
A = np.zeros((2 * ns, ne))
for e, (u, v) in enumerate(edges):
    dx, dy = float(dirs[e][0]), float(dirs[e][1])
    for node, sgn in ((u, -1.0), (v, +1.0)):
        if na <= node < na + ns:
            rr = node - na
            A[2 * rr, e] += sgn * dx
            A[2 * rr + 1, e] += sgn * dy

# ---------------- gap derivatives: tau_i then g_k = sum_{i>k} tau_i
def gap_fun(alpha, ndig=50):
    """alpha: mp list -> (taus, g) in mp"""
    mp.mp.dps = ndig
    tau = [mp.mpf(0)] * na
    for e, (u, v) in enumerate(edges):
        d = dirs[e]
        for node in (u, v):
            if node < na:
                a = anchors[node]
                t = (-a[1], a[0])
                cr = d[0] * t[1] - d[1] * t[0]
                tau[node] += 2 * alpha[e] * cr
    gg = [mp.mpf(0)] * na
    for k in range(na):
        gg[k] = sum(tau[k + 1:])
    return tau, gg

# sanity: sum of all taus = 0 (rotation invariance) for any alpha
al_test = [mp.mpf(1) / ne] * ne
tau_t, g_t = gap_fun(al_test)
W("")
W("sanity: sum tau = %s (expect 0) ; g_9 = %s (expect 0)" % (mp.nstr(sum(tau_t), 6), mp.nstr(g_t[-1], 6)))

# sanity: A alpha = 0 for a random alpha? (no) -- instead check A's row sums logic via a known stress
# ---------------- KKT LP
# variables: alpha(ne), c(1).  equalities: A alpha = 0 ; g_k - c = 0 for k in I -> linear in alpha
I = [0, 1, 2, 3, 5, 6, 7, 8]
Acap = [4, 9]
# build g as a linear map (exactly, via float for LP)
G = np.zeros((na, ne))
for e, (u, v) in enumerate(edges):
    # tau_i contribution coefficient of alpha_e, for each anchor i
    tcoef = [0.0] * na
    d = dirs[e]
    for node in (u, v):
        if node < na:
            a = anchors[node]
            t = (-a[1], a[0])
            cr = d[0] * t[1] - d[1] * t[0]
            tcoef[node] += 2 * float(cr)
    for k in range(na):
        G[k, e] = sum(tcoef[k + 1:])
# verify G alpha == g
gv = G @ np.array([float(x) for x in al_test])
W("sanity: max |G alpha_test - g| = %.3e" % max(abs(gv[k] - float(g_t[k])) for k in range(na)))

from scipy.optimize import linprog
Aeq = np.zeros((2 * ns + len(I), ne + 1))
Aeq[:2 * ns, :ne] = A
for row, k in enumerate(I):
    Aeq[2 * ns + row, :ne] = G[k, :]
    Aeq[2 * ns + row, ne] = -1.0
beq = np.zeros(2 * ns + len(I))
# inequalities: g_k - c <= 0 for k in Acap ; -alpha <= 0
Aub = np.zeros((len(Acap) + ne, ne + 1))
for row, k in enumerate(Acap):
    Aub[row, :ne] = G[k, :]
    Aub[row, ne] = -1.0
Aub[len(Acap):, :ne] = -np.eye(ne)
bub = np.zeros(len(Acap) + ne)
cobj = np.zeros(ne + 1)
cobj[ne] = -1.0     # maximise c (free variable)
res = linprog(cobj, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
              bounds=[(0, None)] * ne + [(None, None)], method="highs")
W("")
W("### LP (variables alpha>=0, c free):")
W("   status=%s  %s" % (res.status, res.message))
if res.status == 0:
    al = res.x[:ne]
    c_star = res.x[ne]
    W("   sum alpha = %.12f ; nonzero entries = %d ; min alpha = %.3e ; c* = %.12f"
      % (al.sum(), int((al > 1e-14).sum()), al.min(), c_star))
else:
    W("   no feasible LP point -> cone empty (numerically)")

# ---------------- exact-precision feasibility assessment
# minimise sum of nonneg alpha over {A a = 0, g_I = c, g_cap <= c}
csum = np.zeros(ne + 1); csum[:ne] = 1.0
res2 = linprog(csum, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
               bounds=[(0, None)] * ne + [(None, None)], method="highs")
W("")
W("### minimise sum(alpha) over the KKT system (0 = only trivial solution):")
if res2.status == 0:
    W("   min sum alpha = %.12e ; support size = %d ; c = %.12f"
      % (res2.fun, int((res2.x[:ne] > 1e-12).sum()), res2.x[ne]))
    al2 = res2.x[:ne]
    # high precision residual check
    Am = [[mp.mpf(float(A[i, j])) for j in range(ne)] for i in range(2 * ns)]
    Gm = [[mp.mpf(float(G[k, j])) for j in range(ne)] for k in range(na)]
    am = [mp.mpf(float(x)) for x in al2]
    cm = mp.mpf(float(res2.x[ne]))
    eq1 = max(abs(sum(Am[i][j] * am[j] for j in range(ne))) for i in range(2 * ns))
    gg = [sum(Gm[k][j] * am[j] for j in range(ne)) for k in range(na)]
    W("   hp: max |A alpha| = %s ; normalisation sum alpha = %s" % (mp.nstr(eq1, 6), mp.nstr(sum(am), 12)))
    W("   g_k - c: %s" % [(k, mp.nstr(gg[k] - cm, 8)) for k in range(na)])
    W("   active-cap multipliers mu_k = g_k - c (must be >= 0): %s" % [(k, mp.nstr(gg[k] - cm, 8)) for k in Acap])
    # structural quantities
    taus, _ = gap_fun(am)
    W("   sum tau = %s" % mp.nstr(sum(taus), 6))
    W("   |alpha|_1 = %s (normalised)" % mp.nstr(sum(am), 10))
    # nullity of the equality system
    M = np.vstack([A, G[I, :]])
    sv = np.linalg.svd(M, compute_uv=False)
    W("   equality matrix %s ; rank=%d nullity=%d" % (M.shape, np.linalg.matrix_rank(M), M.shape[1] - np.linalg.matrix_rank(M)))
    W("   smallest singular values: %s" % [float(x) for x in sv[-6:]])
else:
    W("   LP infeasible -> empty")

data = dict(r=mp.nstr(r, 40), L=mp.nstr(L, 30), ne=ne,
            faces=[list(f) for f in FACES],
            switches=[mp.nstr(a, 20) for a in SWITCH],
            owners=owners,
            witnesses=[[mp.nstr(w[0], 30), mp.nstr(w[1], 30)] for w in WITS],
            lp_status=int(res.status), lp_min_sum=(float(res2.fun) if res2.status == 0 else None))
(HERE.parent / "evidence/n14kkt.json").write_text(json.dumps(data, indent=1), encoding="utf-8")
(HERE.parent / "logs/n14kkt.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/n14kkt.txt")
