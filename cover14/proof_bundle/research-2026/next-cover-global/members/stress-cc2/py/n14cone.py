"""n14cone.py -- final: linear structure of the KKT cone, a concrete stress, and curvature with a
well-conditioned stress.
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
for k, f in enumerate(FACES):
    for j in f:
        edges.append((na + ns + k, na + j))
ne = len(edges)
Z = list(AN) + list(C) + list(WI)
anch_deg = {j: sum(1 for (i, jj) in tp if jj == j) for j in range(14)}
free_sites = [j for j in range(14) if anch_deg[j] > 0]
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

I = [0, 1, 2, 3, 5, 6, 7, 8]; AC = [4, 9]
Me = np.vstack([A, G[I, :]])
U, S, Vt = np.linalg.svd(Me)
rank = int((S > 1e-9 * S[0]).sum())
Ns = Vt[rank:]
W("== n14 KKT cone linear structure ==")
W("equality system [A; G_I]: %s ; rank=%d ; nullity=%d" % (Me.shape, rank, ne - rank))
W("smallest 8 singular values: %s" % [float(x) for x in S[-8:]])
# is there a nonneg element of the nullspace with g_4, g_9 >= 0?
from scipy.optimize import linprog
Aeq = np.vstack([Me, np.ones(ne)]); beq = np.hstack([np.zeros(ranklike := Me.shape[0]), 1.0])
Aub = np.vstack([-np.eye(ne), [-G[4, :], -G[9, :]]])
bub = np.zeros(ne + 2)
rr0 = linprog(np.zeros(ne), A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * ne, method="highs")
W("KKT cone nonempty: %s" % (rr0.status == 0))
# maximise the minimum component with an explicit floor
lo, hi = 0.0, 1e-3
for _ in range(70):
    mid = 0.5 * (lo + hi)
    Ab = np.vstack([Aub, -np.eye(ne)])
    bb = np.hstack([bub, -mid * np.ones(ne)])
    rr = linprog(np.zeros(ne), A_ub=Ab, b_ub=bb, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * ne, method="highs")
    if rr.status == 0:
        lo = mid
    else:
        hi = mid
W("max uniform floor t* = %.3e (proxy for the cone's 'thickness')" % lo)
# extremal-ish elements: maximise alpha_e with a floor 1e-3 * t*
alpha_candidates = []
for tgt in range(ne):
    c = np.zeros(ne); c[tgt] = -1.0
    Ab = np.vstack([Aub, -np.eye(ne)])
    bb = np.hstack([bub, -max(lo * 1e-3, 1e-12) * np.ones(ne)])
    rr = linprog(c, A_ub=Ab, b_ub=bb, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * ne, method="highs")
    if rr.status == 0:
        alpha_candidates.append(rr.x)
cands = np.array(alpha_candidates)
support_sizes = [(int((v > 1e-12).sum()), i) for i, v in enumerate(cands)]
W("candidate KKT stresses: %d ; float support sizes (sorted, top 8): %s" % (
    len(cands), sorted(support_sizes, reverse=True)[:8]))
# choose the richest
best_i = max(support_sizes)[1]
alpha_np = cands[best_i]
alpha_np = alpha_np / alpha_np.sum()
W("chosen stress: support %d of %d" % (int((alpha_np > 1e-12).sum()), ne))
# hp verify
al = [mp.mpf(float(x)) for x in alpha_np]
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
W("hp max |equilibrium| = %s" % mp.nstr(max(res), 6))
taus = [mp.mpf(0)] * na
for e2, (u, v) in enumerate(edges):
    for node in (u, v):
        if node < na:
            a = AN[node]; t = (-a[1], a[0])
            taus[node] += 2 * al[e2] * (dmp[e2][0] * t[0] + dmp[e2][1] * t[1])
gtot = sum(taus)
gg = [sum(taus[k + 1:]) for k in range(na)]
W("hp sum tau = %s ; g_cap = [%s, %s] (both must be >= 0)" % (
    mp.nstr(gtot, 6), mp.nstr(gg[4], 8), mp.nstr(gg[9], 8)))

# ---- curvature with this stress
def energy(D, alpha=al):
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
        a_e = alpha[e]
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
        const += a_e * (bx * bx + by * by)
        terms = []
        if iu is not None:
            terms += [(iu, mp.mpf(1)), (iu + 1, mp.mpf(1))]
        if iv is not None:
            terms += [(iv, mp.mpf(-1)), (iv + 1, mp.mpf(-1))]
        for j, sx in terms:
            lin[j] += 2 * a_e * (bx if j % 2 == 0 else by) * sx
        for j, sx in terms:
            for l, sy in terms:
                if (j % 2) == (l % 2):
                    Hm[j][l] += a_e * sx * sy
    M = mp.matrix(Hm)
    try:
        x = mp.lu_solve(M, mp.matrix([-t for t in lin]))
    except ZeroDivisionError:
        return None
    return const + sum(lin[j] * x[j] for j in range(nv)) + sum(x[j] * Hm[j][l] * x[l] for j in range(nv) for l in range(nv))

# gap coordinates: use the ACTUAL cyclic gaps of the candidate anchors (no 2pi-wrapping subtraction)
ans = [a * mp.pi / 180 for a in SW]
GAPV = [(ans[(k + 1) % 10] - ans[k]) % (2 * mp.pi) for k in range(10)]
assert abs(sum(GAPV) - 2 * mp.pi) < mp.mpf("1e-12"), mp.nstr(sum(GAPV) - 2 * mp.pi, 6)
D0v = GAPV[1:]
E0 = energy(D0v)
W("")
W("### curvature with this KKT stress")
if E0 is None:
    W("   Dirichlet block still singular -> curvature not defined for this stress point")
else:
    W("   E(D_base) = %s ; sum(alpha) r*^2 = %s ; diff = %s" % (
        mp.nstr(E0, 20), mp.nstr(sum(al) * r * r, 20), mp.nstr(E0 - sum(al) * r * r, 6)))
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
                    vv = energy(Dp)
                    if vv is None:
                        acc = None; break
                    acc += sk * sl * vv
                if acc is None:
                    break
            if acc is None:
                H[k][l] = H[l][k] = None
                continue
            v = acc / (4 * h2 * h2); H[k][l] = v; H[l][k] = v
    if all(H[i][j] is not None for i in range(9) for j in range(9)):
        Hn = np.array([[float(H[i][j]) for j in range(9)] for i in range(9)])
        W("   Hessian eigenvalues (9 free gaps): %s" % ["%.6e" % x for x in np.linalg.eigvalsh(Hn)])
        sel = [k for k in range(9) if k not in [4, 9]]
        evc = np.linalg.eigvalsh(Hn[np.ix_(sel, sel)])
        W("   critical cone (gaps 4,9 fixed) eigenvalues: %s" % ["%.6e" % x for x in evc])
        W("   lambda_min on critical cone = %.6e" % evc[0])
    else:
        W("   some Hessian entries undefined (Dirichlet singular at a perturbed point)")

json.dump(dict(rank=rank, nullity=ne - rank, t_star=float(lo),
               support=int((alpha_np > 1e-12).sum()),
               alpha=[float(x) for x in alpha_np],
               edges=[[int(u), int(v)] for (u, v) in edges],
               g=[float(x) for x in [G[k] @ alpha_np for k in range(na)]]),
          open(HERE.parent / "evidence/n14cone.json", "w"), indent=1)
(HERE.parent / "logs/n14cone.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/n14cone.txt")

