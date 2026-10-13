"""n14kkt2.py -- n14 capped-simplex KKT stress at the NEW stationary root (corrected tau).

Network: 10 boundary anchors, 14 sites, 14 tight interior witnesses, 62 edges (all of length r*).
Unknowns: alpha (62 edge stresses, >=0), c (free multiplier).
System:
  (E1) A alpha = 0                      equilibrium at the 14 free sites (28 rows)
  (E2) g_k - c = 0, k in I={0,1,2,3,5,6,7,8}   interior gaps (inactive caps)
  (E3) g_k - c <= 0, k in {4,9}          cap-active gaps (two active caps)
  (N)  sum alpha = 1
Feasibility of (E1)-(E3)+(N) with alpha>=0 is what decides whether a single constant stress
supports the candidate; the cone is homogeneous so (N) only kills the trivial alpha=0 point.
"""
import json, sys
from pathlib import Path
import numpy as np
import mpmath as mp

mp.mp.dps = 60
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom import new_geom, centers_from, dist, norm

g = new_geom(); C = centers_from(g); r = g["r"]; L = 2 * mp.asin(r)
OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

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
    s = mp.lu_solve(A, b); return (s[0], s[1])

WITS = [circum([C[i] for i in f]) for f in FACES]
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
dirs = []
for (u, v) in edges:
    dv = (Z[v][0] - Z[u][0], Z[v][1] - Z[u][1])
    n_ = mp.sqrt(dv[0] ** 2 + dv[1] ** 2)
    dirs.append((dv[0] / n_, dv[1] / n_))
lens = [mp.sqrt((Z[v][0] - Z[u][0]) ** 2 + (Z[v][1] - Z[u][1]) ** 2) for (u, v) in edges]

W("== n14 capped-simplex KKT (corrected tau = d . t) ==")
W("r*= %s ; L*= %s ; cap-active gaps {4,9}" % (mp.nstr(r, 30), mp.nstr(L, 25)))
W("edges=%d (anchor-site %d, witness-site %d) ; max |len - r*| = %s (float coords)"
  % (ne, 2 * na, 3 * nw, mp.nstr(max(abs(x - r) for x in lens), 4)))
# gap values from the anchors (used only as a diagnostic of cap activity)
angs = [mp.atan2(a[1], a[0]) % (2 * mp.pi) for a in anchors]
gaps = [(angs[(k + 1) % na] - angs[k]) % (2 * mp.pi) for k in range(na)]
W("gaps deg = %s" % [mp.nstr(x * 180 / mp.pi, 10) for x in gaps])
W("gap - L* = %s" % [mp.nstr(x - L, 4) for x in gaps])

# ---- equilibrium matrix A and gap-derivative matrix G
A = np.zeros((2 * ns, ne))
G = np.zeros((na, ne))
for e, (u, v) in enumerate(edges):
    dx, dy = float(dirs[e][0]), float(dirs[e][1])
    for node, sgn in ((u, -1.0), (v, +1.0)):
        if na <= node < na + ns:
            rr = node - na
            A[2 * rr, e] += sgn * dx
            A[2 * rr + 1, e] += sgn * dy
# tau_i coefficient, then g_k = sum_{i>k} tau_i  (correct: d . t)
tcoef = np.zeros((na, ne))
for e, (u, v) in enumerate(edges):
    d = dirs[e]
    for node in (u, v):
        if node < na:
            a = anchors[node]
            t = (-a[1], a[0])
            tcoef[node, e] += 2 * float(d[0] * t[0] + d[1] * t[1])
for k in range(na):
    G[k, :] = tcoef[k + 1:, :].sum(0)

# sanity in mp with uniform alpha
amp = [mp.mpf(1) / ne] * ne
tau = [sum(2 * amp[e] * (dirs[e][0] * (-anchors[i][1]) + dirs[e][1] * anchors[i][0])
           for e, (u, v) in enumerate(edges) if u == i or v == i) for i in range(na)]
W("")
W("sanity: sum tau = %s (expect 0 by rotation invariance)" % mp.nstr(sum(tau), 6))
gg = G @ np.array([float(x) for x in amp])
W("        g_9 = %.3e (expect 0) ; max|G a - g| checked separately" % gg[-1])

I = [0, 1, 2, 3, 5, 6, 7, 8]
AC = [4, 9]

# ---- LP 1: feasibility (max alpha-uniform lower bound is wrong here because sum alpha = 1 is the
# normalisation); use: find any alpha>=0 with A a=0, g_I - c = 0, g_AC - c <= 0, sum a = 1.
from scipy.optimize import linprog
rows = 2 * ns + len(I) + 1
Aeq = np.zeros((rows, ne + 1))
Aeq[:2 * ns, :ne] = A
for kk, k in enumerate(I):
    Aeq[2 * ns + kk, :ne] = G[k, :]
    Aeq[2 * ns + kk, ne] = -1.0
Aeq[-1, :ne] = 1.0
beq = np.zeros(rows); beq[-1] = 1.0
Aub = np.zeros((len(AC) + ne, ne + 1))
for kk, k in enumerate(AC):
    Aub[kk, :ne] = G[k, :]; Aub[kk, ne] = -1.0
Aub[len(AC):, :ne] = -np.eye(ne)
bub = np.zeros(len(AC) + ne)
res = linprog(np.zeros(ne + 1), A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
              bounds=[(0, None)] * ne + [(None, None)], method="highs")
W("")
W("### feasibility LP (alpha>=0, sum alpha=1): status=%s" % res.status)
if res.status == 0:
    al = res.x[:ne]; cst = res.x[ne]
    W("   FEASIBLE. support=%d ; min alpha=%.6e ; max alpha=%.6f ; c=%.8f"
      % (int((al > 1e-13).sum()), al.min(), al.max(), cst))
    W("   support edges: %s" % [e for e in range(ne) if al[e] > 1e-13])
else:
    W("   INFEASIBLE numerically -> cone empty (needs exact/Farkas confirmation)")

# ---- LP 2: minimise the max violation of the cap inequalities (soft feasibility)
# variables alpha>=0, c free, s>=0 ; g_k - c <= s (k in AC) ; sum alpha = 1 ; minimise s
Aub2 = np.zeros((len(AC) + ne, ne + 2))
for kk, k in enumerate(AC):
    Aub2[kk, :ne] = G[k, :]; Aub2[kk, ne] = -1.0; Aub2[kk, ne + 1] = -1.0
Aub2[len(AC):, :ne] = -np.eye(ne)
bub2 = np.zeros(len(AC) + ne)
Aeq2 = np.zeros((2 * ns + len(I) + 1, ne + 2))
Aeq2[:2 * ns, :ne] = A
for kk, k in enumerate(I):
    Aeq2[2 * ns + kk, :ne] = G[k, :]; Aeq2[2 * ns + kk, ne] = -1.0
Aeq2[-1, :ne] = 1.0
beq2 = np.zeros(2 * ns + len(I) + 1); beq2[-1] = 1.0
cobj = np.zeros(ne + 2); cobj[ne + 1] = 1.0
res2 = linprog(cobj, A_ub=Aub2, b_ub=bub2, A_eq=Aeq2, b_eq=beq2,
               bounds=[(0, None)] * ne + [(None, None), (0, None)], method="highs")
W("")
W("### minimum cap violation s* (0 <=> KKT cone nonempty):")
if res2.status == 0:
    W("   s* = %.12e ; support=%d ; c=%.10f" % (res2.fun, int((res2.x[:ne] > 1e-13).sum()), res2.x[ne]))
    al2 = res2.x[:ne]
    gg2 = G @ al2
    W("   active-cap gaps: g_4-c = %.6e ; g_9-c = %.6e" % (gg2[4] - res2.x[ne], gg2[9] - res2.x[ne]))
    W("   support edges: %s" % [e for e in range(ne) if al2[e] > 1e-13])

# ---- LP 3: unconstrained nonneg equilibrium only (no KKT): does any stress exist?
res3 = linprog(np.zeros(ne), A_eq=np.vstack([A, np.ones(ne)]), b_eq=np.hstack([np.zeros(2 * ns), 1.0]),
               bounds=[(0, None)] * ne, method="highs")
W("")
W("### nonneg equilibrium only (no KKT): status=%s" % res3.status)
if res3.status == 0:
    al3 = res3.x
    W("   exists; support=%d ; min=%.4e" % (int((al3 > 1e-13).sum()), al3.min()))
    gg3 = G @ al3
    W("   g = %s" % ["%.6f" % x for x in gg3])

# ---- LP 4: maximum uniform t over ALL edges (strictly positive stress?), normalised by sum=1
Aub4 = np.zeros((ne, ne + 1)); Aub4[:, :ne] = -np.eye(ne); Aub4[:, ne] = 1.0
Aeq4 = np.zeros((2 * ns + 1, ne + 1)); Aeq4[:2 * ns, :ne] = A; Aeq4[-1, :ne] = 1.0
beq4 = np.zeros(2 * ns + 1); beq4[-1] = 1.0
c4 = np.zeros(ne + 1); c4[ne] = -1.0
res4 = linprog(c4, A_ub=Aub4, b_ub=np.zeros(ne), A_eq=Aeq4, b_eq=beq4,
               bounds=[(0, None)] * ne + [(None, None)], method="highs")
W("")
W("### max uniform edge weight t_max over nonneg equilibrium (sum=1): %s"
  % ("%.10e" % res4.x[-1] if res4.status == 0 else "infeasible"))

# ---- structural: nullity of the equilibrium system
sv = np.linalg.svd(A, compute_uv=False)
W("")
W("### rank/nullity (float SVD; NOT an exact rank statement):")
W("   A is %s ; rank=%d ; nullity=%d ; smallest sv = %s"
  % (A.shape, np.linalg.matrix_rank(A), ne - np.linalg.matrix_rank(A), [float(x) for x in sv[-6:]]))
M2 = np.vstack([A, G[I, :]])
sv2 = np.linalg.svd(M2, compute_uv=False)
W("   [A; G_I] is %s ; rank=%d ; nullity=%d ; smallest sv = %s"
  % (M2.shape, np.linalg.matrix_rank(M2), ne - np.linalg.matrix_rank(M2), [float(x) for x in sv2[-8:]]))

data = dict(r=mp.nstr(r, 40), L=mp.nstr(L, 30), ne=ne, na=na, ns=ns, nw=nw,
            faces=[list(f) for f in FACES], owners=owners, cap_active=AC, interior=I,
            lp_feasible_status=int(res.status),
            lp_min_cap_violation=(float(res2.fun) if res2.status == 0 else None),
            lp_nonneg_equilibrium_status=int(res3.status),
            t_max=(float(res4.x[-1]) if res4.status == 0 else None),
            A_shape=list(A.shape), A_rank_float=int(np.linalg.matrix_rank(A)))
(HERE.parent / "evidence/n14kkt2.json").write_text(json.dumps(data, indent=1), encoding="utf-8")
(HERE.parent / "logs/n14kkt2.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/n14kkt2.txt")
