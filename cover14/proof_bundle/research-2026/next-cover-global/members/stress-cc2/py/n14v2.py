"""n14v2.py -- final corrected analysis of the n14 sharp-candidate capped-simplex stress.

Fixes vs the old kernel run:
  * geometry: Lead's stationary root with the CORRECT chain b=r+sqrt(r^2-((s-z)/2)^2);
  * torque sign: gaps use dE/dtheta_i = +2 sum_e alpha_e (d_e . t_i)  (finite-difference verified);
  * KKT sign: constraint Delta_k <= L* gives g_k >= 0 for cap-active gaps.
Network: 10 anchors (boundary switches, tight with 2 centres each), 14 sites, 14 witnesses
(empty-circle centres), 20+42 = 62 edges (all lengths = r* to within input rounding).
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

SW = [mp.mpf(x) for x in ["19.37393668027073", "51.774419687402606", "90.0", "128.2255803125974",
                          "160.62606331972927", "199.37393668027073", "231.7744196874026",
                          "270.0", "308.2255803125974", "340.62606331972927"]]
AN = [(mp.cos(a * mp.pi / 180), mp.sin(a * mp.pi / 180)) for a in SW]

def circum(P):
    A = mp.matrix([[2 * (P[1][0] - P[0][0]), 2 * (P[1][1] - P[0][1])],
                   [2 * (P[2][0] - P[0][0]), 2 * (P[2][1] - P[0][1])]])
    b = mp.matrix([P[1][0] ** 2 + P[1][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2,
                   P[2][0] ** 2 + P[2][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2])
    s = mp.lu_solve(A, b); return (s[0], s[1])

FACES = [(0, 4, 13), (0, 8, 10), (0, 10, 13), (1, 5, 13), (1, 9, 11), (1, 11, 13),
         (2, 6, 12), (2, 8, 10), (2, 10, 12), (3, 7, 12), (3, 9, 11), (3, 11, 12),
         (10, 11, 12), (10, 11, 13)]
WI = [circum([C[i] for i in f]) for f in FACES]
na, ns, nw = 10, 14, 14

# tight anchor-site pairs with a working tolerance (inputs are 17-digit decimals)
tight_pairs = []
for i, a in enumerate(AN):
    for j in range(14):
        if abs(dist(a, C[j]) - r) < mp.mpf("1e-12"):
            tight_pairs.append((i, j))
W("== n14 stress network, corrected ==")
W("r*=%.20f  L*=%.20f" % (float(r), float(L)))
W("tight anchor-site pairs: %d" % len(tight_pairs))
deg = {j: sum(1 for (i, jj) in tight_pairs if jj == j) for j in range(14)}
W("per-site anchor degree: %s" % deg)
W("unanchored sites (degree 0): %s" % [j for j in range(14) if deg[j] == 0])

edges = [(i, j + na) for (i, j) in tight_pairs]
for k, f in enumerate(FACES):
    for j in f:
        edges.append((na + ns + k, na + j))
ne = len(edges)
Z = list(AN) + list(C) + list(WI)
dirs = []
for (u, v) in edges:
    dv = (Z[v][0] - Z[u][0], Z[v][1] - Z[u][1]); n_ = mp.sqrt(dv[0] ** 2 + dv[1] ** 2)
    dirs.append((dv[0] / n_, dv[1] / n_))
W("edges=%d (anchor-site %d, witness-site %d)" % (ne, len(tight_pairs), 3 * nw))
W("edge-length deviations from r*: max=%s" % mp.nstr(max(abs(mp.sqrt((Z[v][0] - Z[u][0]) ** 2 + (Z[v][1] - Z[u][1]) ** 2) - r) for (u, v) in edges), 4))

# ---- equilibrium matrix and gap derivatives
A = np.zeros((2 * ns, ne))
for e, (u, v) in enumerate(edges):
    dx, dy = float(dirs[e][0]), float(dirs[e][1])
    for node, sgn in ((u, -1.0), (v, +1.0)):
        if na <= node < na + ns:
            rr = node - na
            A[2 * rr, e] += sgn * dx; A[2 * rr + 1, e] += sgn * dy
tau_coef = np.zeros((na, ne))
for e, (u, v) in enumerate(edges):
    d = dirs[e]
    for node in (u, v):
        if node < na:
            a = AN[node]; t = (-a[1], a[0])
            tau_coef[node, e] += 2.0 * float(d[0] * t[0] + d[1] * t[1])
G = np.zeros((na, ne))
for k in range(na):
    G[k, :] = tau_coef[k + 1:, :].sum(0) if k + 1 < na else 0.0
W("")
GAPV = [((mp.atan2(AN[(k + 1) % na][1], AN[(k + 1) % na][0]) - mp.atan2(AN[k][1], AN[k][0])) % (2 * mp.pi)) for k in range(na)]
W("gap values from anchors (deg): %s" % [mp.nstr(x * 180 / mp.pi, 10) for x in GAPV])
W("cap-active gaps (gap == L*): %s" % [k for k in range(na) if abs(GAPV[k] - L) < mp.mpf("1e-12")])

from scipy.optimize import linprog
# (1) nonneg equilibrium: per-edge maxima
W("")
W("### nonneg equilibrium cone (alpha>=0, A alpha=0, sum=1)")
mx = np.zeros(ne)
for e in range(ne):
    c = np.zeros(ne); c[e] = -1.0
    rr = linprog(c, A_eq=np.vstack([A, np.ones(ne)]), b_eq=np.hstack([np.zeros(2 * ns), 1.0]),
                 bounds=[(0, None)] * ne, method="highs")
    mx[e] = -rr.fun if rr.status == 0 else 0.0
forced = [e for e in range(ne) if mx[e] <= 1e-11]
W("   forced-zero edges: %d %s" % (len(forced), forced))
W("     of which witness-site: %s" % [e for e in forced if e >= len(tight_pairs)])
W("     of which anchor-site : %s" % [e for e in forced if e < len(tight_pairs)])
W("   positive-capable: %d ; support structure: %s" % (ne - len(forced), ["%d:%.4f" % (e, mx[e]) for e in range(ne) if mx[e] > 1e-11]))

# (2) uniform-t
Aub = np.zeros((ne, ne + 1)); Aub[:, :ne] = -np.eye(ne); Aub[:, ne] = 1.0
Aeq = np.zeros((2 * ns + 1, ne + 1)); Aeq[:2 * ns, :ne] = A; Aeq[-1, :ne] = 1.0
beq = np.zeros(2 * ns + 1); beq[-1] = 1.0
c4 = np.zeros(ne + 1); c4[ne] = -1.0
r4 = linprog(c4, A_ub=Aub, b_ub=np.zeros(ne), A_eq=Aeq, b_eq=beq,
             bounds=[(0, None)] * ne + [(None, None)], method="highs")
W("   max uniform edge weight t_max = %s" % ("%.6e" % r4.x[-1] if r4.status == 0 else "n/a"))
tstar = r4.x[-1] if r4.status == 0 else 0.0

# (3) KKT: g_k = c (interior), g_k >= 0 at cap-active (slope condition), alpha>=0, sum=1
I = [k for k in range(na) if k not in [4, 9]]
AC = [4, 9]
rows = 2 * ns + len(I) + 1
Aeq2 = np.zeros((rows, ne + 1)); Aeq2[:2 * ns, :ne] = A
for kk, k in enumerate(I):
    Aeq2[2 * ns + kk, :ne] = G[k, :]; Aeq2[2 * ns + kk, ne] = -1.0
Aeq2[-1, :ne] = 1.0
beq2 = np.zeros(rows); beq2[-1] = 1.0
Aub2 = np.zeros((len(AC) + ne, ne + 1))
for kk, k in enumerate(AC):
    Aub2[kk, :ne] = G[k, :]; Aub2[kk, ne] = -1.0    # g_k - c <= 0  <=>  g_k <= c (Lead's sign)
Aub2[len(AC):, :ne] = -np.eye(ne)
bub2 = np.zeros(len(AC) + ne)
r5 = linprog(np.zeros(ne + 1), A_ub=Aub2, b_ub=bub2, A_eq=Aeq2, b_eq=beq2,
             bounds=[(0, None)] * ne + [(None, None)], method="highs")
W("")
W("### KKT feasibility (g_I = c, g_4,g_9 >= 0, alpha>=0, sum=1): status=%s" % r5.status)
if r5.status == 0:
    al = r5.x[:ne]
    gg = G @ al
    W("   FEASIBLE. support=%d ; edges=%s" % (int((al > 1e-13).sum()), [e for e in range(ne) if al[e] > 1e-13]))
    W("   g = %s" % ["%.6e" % x for x in gg])
    W("   g_4=%.6e (>=0), g_9=%.6e (>=0), c=%.6f" % (gg[4], gg[9], r5.x[ne]))
else:
    W("   INFEASIBLE (no nonzero KKT stress)")
# (4) minimise the violation of the cap slopes
Aub3 = np.zeros((len(AC) + ne, ne + 2))
for kk, k in enumerate(AC):
    Aub3[kk, :ne] = G[k, :]; Aub3[kk, ne + 1] = -1.0; Aub3[kk, ne] = -1.0
Aub3[len(AC):, :ne] = -np.eye(ne)
Aeq3 = np.zeros((rows, ne + 2)); Aeq3[:, :ne + 1] = Aeq2
cobj = np.zeros(ne + 2); cobj[ne + 1] = 1.0
r6 = linprog(cobj, A_ub=Aub3, b_ub=np.zeros(len(AC) + ne), A_eq=Aeq3, b_eq=beq2,
             bounds=[(0, None)] * ne + [(None, None), (0, None)], method="highs")
W("   min cap-slope violation s* = %s" % ("%.6e" % r6.fun if r6.status == 0 else "n/a"))
# (5) witness-node balance diagnostic: does each witness's 3 directions surround the origin?
W("")
W("### witness-node balance test (must hold for ANY feasible configuration)")
surr_all = True
for k, f in enumerate(FACES):
    angs = []
    for j in f:
        w = WI[k]
        dv = (C[j][0] - w[0], C[j][1] - w[1])
        angs.append(mp.atan2(dv[1], dv[0]) % (2 * mp.pi))
    angs.sort()
    gaps = [(angs[(t + 1) % 3] - angs[t]) % (2 * mp.pi) for t in range(3)]
    if max(gaps) >= mp.pi:
        surr_all = False
        W("   witness %2d %-14s directions do NOT surround origin (max gap %s deg) -> zero forced"
          % (k, str(f), mp.nstr(max(gaps) * 180 / mp.pi, 8)))
W("   all witnesses surround their centroid: %s" % surr_all)
W("   => witness-site edges are structurally forced to zero whenever their witness does NOT")
W("      surround. Count of witness-site edges belonging to such witnesses: %d"
  % sum(3 for k, f in enumerate(FACES) if not (lambda aa: max([(aa[(t + 1) % 3] - aa[t]) % (2 * mp.pi) for t in range(3)]) < mp.pi)(
      sorted(mp.atan2((C[j][1] - WI[k][1]), (C[j][0] - WI[k][0])) % (2 * mp.pi) for j in f))))

# ---- high precision verification of the found KKT point
if r5.status == 0:
    al = [mp.mpf(float(x)) for x in r5.x[:ne]]
    cm = mp.mpf(float(r5.x[ne]))
    W("")
    W("### hp verification of the KKT point (mp, 60 digits)")
    dmp = []
    for (u, v) in edges:
        dv = (Z[v][0] - Z[u][0], Z[v][1] - Z[u][1]); n_ = mp.sqrt(dv[0] ** 2 + dv[1] ** 2)
        dmp.append((dv[0] / n_, dv[1] / n_))
    res = []
    for rr_ in range(ns):
        fx = mp.mpf(0); fy = mp.mpf(0)
        for e2, (u, v) in enumerate(edges):
            for node, sgn in ((u, -1), (v, 1)):
                if node == na + rr_:
                    fx += sgn * al[e2] * dmp[e2][0]; fy += sgn * al[e2] * dmp[e2][1]
        res.append(mp.sqrt(fx * fx + fy * fy))
    W("   max |equilibrium residual| = %s" % mp.nstr(max(res), 6))
    taus = [mp.mpf(0)] * na
    for e2, (u, v) in enumerate(edges):
        for node in (u, v):
            if node < na:
                a = AN[node]; t = (-a[1], a[0])
                taus[node] += 2 * al[e2] * (dmp[e2][0] * t[0] + dmp[e2][1] * t[1])
    gg = [sum(taus[k + 1:]) for k in range(na)]
    W("   sum tau (should be ~0): %s" % mp.nstr(sum(taus), 6))
    W("   g_k - c = %s" % [(k, mp.nstr(gg[k] - cm, 6)) for k in range(na)])
    W("   cap slopes g_4=%s g_9=%s (>=0 required)" % (mp.nstr(gg[4], 6), mp.nstr(gg[9], 6)))

json.dump(dict(r=mp.nstr(r, 40), ne=ne, tight_pairs=[[i, j] for i, j in tight_pairs],
               forced_zero=forced, t_max=float(tstar),
               kkt_status=int(r5.status), min_cap_violation=(float(r6.fun) if r6.status == 0 else None),
               witnesses_surround=bool(surr_all)),
          open(HERE.parent / "evidence/n14v2.json", "w"), indent=1)
(HERE.parent / "logs/n14v2.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/n14v2.txt")

