"""n14fin2.py -- final: KKT cone structure (nonneg equilibrium, KKT, per-edge max) + curvature.

Hierarchy of stress cones over the 62-edge network (20 anchor-site + 42 witness-site):
  C1 = {alpha >= 0 : A alpha = 0}                      (nonneg equilibrium)
  C2 = C1 ∩ {g_k = c (k in I), g_4 >= 0, g_9 >= 0}     (capped-simplex KKT; g = gap slopes)
Also: linear equality structure, forced-zero edges, and the local curvature of
  E(theta) = sum_e alpha_e |e(theta)|^2   (witnesses and unanchored sites fixed,
  anchored sites Dirichlet-eliminated) on the sharp domain in gap coordinates.
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
na, ns = 10, 14
tp = [(i, j) for i in range(10) for j in range(14) if abs(dist(AN[i], C[j]) - r) < mp.mpf("1e-12")]
edges = [(i, j + na) for (i, j) in tp]
face_edge_off = {}
for k, f in enumerate(FACES):
    for j in f:
        face_edge_off[(k, j)] = len(edges)
        edges.append((na + ns + k, na + j))
ne = len(edges)
Z = list(AN) + list(C) + list(WI)
anch_deg = {j: sum(1 for (i, jj) in tp if jj == j) for j in range(14)}
free_sites = [j for j in range(14) if anch_deg[j] > 0]
W("== n14 final structural analysis ==")
W("anchored sites: %s ; unanchored: %s" % (free_sites, [j for j in range(14) if anch_deg[j] == 0]))
W("edges: %d (anchor-site %d, witness-site %d)" % (ne, len(tp), 3 * 14))

A = np.zeros((2 * ns, ne)); G = np.zeros((na, ne))
for e, (u, v) in enumerate(edges):
    dv = (Z[v][0] - Z[u][0], Z[v][1] - Z[u][1]); n_ = mp.sqrt(dv[0] ** 2 + dv[1] ** 2)
    d = (dv[0] / n_, dv[1] / n_)
    for node, sgn in ((u, -1.0), (v, +1.0)):
        if na <= node < na + ns:
            rr = node - na
            A[2 * rr, e] += sgn * float(d[0]); A[2 * rr + 1, e] += sgn * float(d[1])
    for node in (u, v):
        if node < na:
            a = AN[node]; t = (-a[1], a[0])
            G[node, e] += 2.0 * float(d[0] * t[0] + d[1] * t[1])
for k in range(na):
    G[k, :] = G[k + 1:, :].sum(0) if k + 1 < na else 0.0

from scipy.optimize import linprog
I = [0, 1, 2, 3, 5, 6, 7, 8]; AC = [4, 9]
Aeq1 = np.vstack([A, np.ones(ne)]); beq1 = np.hstack([np.zeros(2 * ns), 1.0])

W("")
W("### C1 = {alpha>=0 : A alpha = 0, sum=1}  (nonneg equilibrium, no KKT)")
mx1 = np.zeros(ne)
for e in range(ne):
    c = np.zeros(ne); c[e] = -1.0
    rr = linprog(c, A_eq=Aeq1, b_eq=beq1, bounds=[(0, None)] * ne, method="highs")
    mx1[e] = -rr.fun if rr.status == 0 else 0.0
fz1 = [e for e in range(ne) if mx1[e] <= 1e-11]
W("   forced-zero edges: %d ; witness-site %d ; anchor-site %d" % (
    len(fz1), sum(1 for e in fz1 if e >= len(tp)), sum(1 for e in fz1 if e < len(tp))))
W("   witness-site edges of which face: %s" % sorted({FACES[(e - len(tp)) // 3] for e in fz1 if e >= len(tp)}))

rows = 2 * ns + len(I) + 1
Aeq2 = np.zeros((rows, ne + 1)); Aeq2[:2 * ns, :ne] = A
for kk, k in enumerate(I):
    Aeq2[2 * ns + kk, :ne] = G[k, :]; Aeq2[2 * ns + kk, ne] = -1.0
Aeq2[-1, :ne] = 1.0
beq2 = np.zeros(rows); beq2[-1] = 1.0
Aub2 = np.zeros((len(AC) + ne, ne + 1))
for kk, k in enumerate(AC):
    Aub2[kk, :ne] = -G[k, :]
Aub2[len(AC):, :ne] = -np.eye(ne)
bub2 = np.zeros(len(AC) + ne)

W("")
W("### C2 = C1 ∩ {g_I = c, g_4>=0, g_9>=0}  (capped-simplex KKT)")
r5 = linprog(np.zeros(ne + 1), A_ub=Aub2, b_ub=bub2, A_eq=Aeq2, b_eq=beq2,
             bounds=[(0, None)] * ne + [(None, None)], method="highs")
W("   feasibility: status=%s (%s)" % (r5.status, "FEASIBLE" if r5.status == 0 else "EMPTY"))
# max uniform t over C2 by bisection
lo, hi = 0.0, 1e-3
for _ in range(60):
    mid = 0.5 * (lo + hi)
    Ab = np.vstack([Aub2, np.hstack([-np.eye(ne), np.zeros((ne, 1))])])
    bb = np.hstack([bub2, -mid * np.ones(ne)])
    rr = linprog(np.zeros(ne + 1), A_ub=Ab, b_ub=bb, A_eq=Aeq2, b_eq=beq2,
                 bounds=[(0, None)] * ne + [(None, None)], method="highs")
    if rr.status == 0:
        lo = mid
    else:
        hi = mid
W("   max uniform edge weight over C2: t* = %.6e" % lo)
# per-edge maxima over C2
mx2 = np.zeros(ne)
for e in range(ne):
    c = np.zeros(ne + 1); c[e] = -1.0
    rr = linprog(c, A_ub=Aub2, b_ub=bub2, A_eq=Aeq2, b_eq=beq2,
                 bounds=[(0, None)] * ne + [(None, None)], method="highs")
    mx2[e] = -rr.fun if rr.status == 0 else 0.0
fz2 = [e for e in range(ne) if mx2[e] <= 1e-11]
W("   edges forced to zero over C2: %d %s" % (len(fz2), fz2))
W("   of which witness-site: %s" % [e for e in fz2 if e >= len(tp)])
W("   edges with positive max over C2: %d" % (ne - len(fz2)))

# ---------------- curvature
W("")
W("### curvature of E(theta) = sum_e alpha_e |e|^2 (witnesses + unanchored sites fixed)")
# take a C2 point with the richest support
bestv = None; bs = -1
for trial in range(20):
    rng = np.random.default_rng(2000 + trial)
    w = rng.random(ne) + 0.1
    c = np.zeros(ne + 1); c[:ne] = -w
    Ab = np.vstack([Aub2, np.hstack([-np.eye(ne), np.zeros((ne, 1))])])
    bb = np.hstack([bub2, -1e-11 * np.ones(ne)])
    rr = linprog(c, A_ub=Ab, b_ub=bb, A_eq=Aeq2, b_eq=beq2,
                 bounds=[(0, None)] * ne + [(None, None)], method="highs")
    if rr.status != 0:
        continue
    s = int((rr.x[:ne] > 1e-12).sum())
    if s > bs:
        bs = s; bestv = rr.x
alpha = [mp.mpf(float(x)) for x in bestv[:ne]]
W("   chosen C2 stress: support=%d of %d" % (bs, ne))

def energy(D):
    td = sum(D); D0 = 2 * mp.pi - td
    gaps = [D0] + list(D)
    th = []; acc = mp.mpf(0)
    for k in range(na):
        acc += gaps[k]; th.append(acc)
    AP = [(mp.cos(t), mp.sin(t)) for t in th]
    idx = {j: 2 * i for i, j in enumerate(free_sites)}
    nv = 2 * len(free_sites)
    Hm = [[mp.mpf(0)] * nv for _ in range(nv)]
    lin = [mp.mpf(0)] * nv; const = mp.mpf(0)
    for e, (u, v) in enumerate(edges):
        al = alpha[e]
        def base(node):
            if node < na:
                return AP[node], None
            if na <= node < na + ns:
                j = node - na
                if j in idx:
                    return None, idx[j]
                return C[j], None
            return WI[node - na - ns], None
        pu, iu = base(u); pv, iv = base(v)
        bx = (pu[0] if pu else mp.mpf(0)) - (pv[0] if pv else mp.mpf(0))
        by = (pu[1] if pu else mp.mpf(0)) - (pv[1] if pv else mp.mpf(0))
        const += al * (bx * bx + by * by)
        terms = []
        if iu is not None:
            terms += [(iu, mp.mpf(1)), (iu + 1, mp.mpf(1))]
        if iv is not None:
            terms += [(iv, mp.mpf(-1)), (iv + 1, mp.mpf(-1))]
        for j, sx in terms:
            lin[j] += 2 * al * (bx if j % 2 == 0 else by) * sx
        for j, sx in terms:
            for l, sy in terms:
                if (j % 2) == (l % 2):
                    Hm[j][l] += al * sx * sy
    M = mp.matrix(Hm)
    try:
        x = mp.lu_solve(M, mp.matrix([-t for t in lin]))
    except ZeroDivisionError:
        return None
    return const + sum(lin[j] * x[j] for j in range(nv)) + sum(x[j] * Hm[j][l] * x[l] for j in range(nv) for l in range(nv))

GAPV = [((mp.atan2(AN[(k + 1) % 10][1], AN[(k + 1) % 10][0]) - mp.atan2(AN[k][1], AN[k][0])) % (2 * mp.pi)) for k in range(10)]
D0v = GAPV[1:]
E0 = energy(D0v)
if E0 is None:
    W("   Dirichlet block singular for this stress -> curvature undefined for this point")
else:
    W("   E(D_base) = %s ; sum(alpha)*r*^2 = %s ; diff = %s" % (
        mp.nstr(E0, 20), mp.nstr(sum(alpha) * r * r, 20), mp.nstr(E0 - sum(alpha) * r * r, 6)))
    h1 = mp.mpf("1e-18"); h2 = mp.mpf("1e-12")
    gr = []
    for k in range(9):
        Dp = list(D0v); Dm = list(D0v); Dp[k] += h1; Dm[k] -= h1
        gr.append((energy(Dp) - energy(Dm)) / (2 * h1))
    W("   gradient = %s" % [mp.nstr(x, 8) for x in gr])
    H = [[mp.mpf(0)] * 9 for _ in range(9)]
    for k in range(9):
        for l in range(k, 9):
            acc = mp.mpf(0)
            for sk in (1, -1):
                for sl in (1, -1):
                    Dp = list(D0v); Dp[k] += sk * h2; Dp[l] += sl * h2
                    acc += sk * sl * energy(Dp)
            v = acc / (4 * h2 * h2); H[k][l] = v; H[l][k] = v
    Hn = np.array([[float(H[i][j]) for j in range(9)] for i in range(9)])
    W("   Hessian eigenvalues (9 free gaps): %s" % ["%.6e" % x for x in np.linalg.eigvalsh(Hn)])
    sel = [k for k in range(9) if k not in [4, 9]]
    evc = np.linalg.eigvalsh(Hn[np.ix_(sel, sel)])
    W("   critical cone (gaps 4,9 fixed at cap) eigenvalues: %s" % ["%.6e" % x for x in evc])
    W("   lambda_min on critical cone = %.6e" % evc[0])

json.dump(dict(r=mp.nstr(r, 40), ne=ne, forced_C1=fz1, forced_C2=fz2, t_star=float(lo),
               support_used=bs), open(HERE.parent / "evidence/n14fin2.json", "w"), indent=1)
(HERE.parent / "logs/n14fin2.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/n14fin2.txt")
