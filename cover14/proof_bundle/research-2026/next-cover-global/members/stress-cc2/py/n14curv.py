"""n14curv.py -- curvature with a correctly parameterised gap domain (anchor 9 angle = 0 gauge).

E(D_1..D_9) = Dirichlet-min energy of sum_e alpha_e |e|^2 with
  anchors at cumulative gap angles, witnesses fixed at candidate empty-circle centres,
  unanchored sites (10..13) fixed at candidate positions, anchored sites eliminated.
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

SWdeg = ["19.37393668027073", "51.774419687402606", "90.0", "128.2255803125974",
         "160.62606331972927", "199.37393668027073", "231.7744196874026",
         "270.0", "308.2255803125974", "340.62606331972927"]
SWr = [mp.mpf(x) * mp.pi / 180 for x in SWdeg]
AN = [(mp.cos(a), mp.sin(a)) for a in SWr]

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

# ---- KKT cone and a chosen stress (recomputed)
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
from scipy.optimize import linprog
Me = np.vstack([A, G[I, :]])
Aeq = np.vstack([Me, np.ones(ne)]); beq = np.hstack([np.zeros(Me.shape[0]), 1.0])
Aub = np.vstack([-np.eye(ne), [-G[4, :], -G[9, :]]]); bub = np.zeros(ne + 2)
# richest support at a small uniform floor
best = None; bs = -1
for tr in range(30):
    rng = np.random.default_rng(500 + tr)
    w = rng.random(ne) + 0.1
    c = np.zeros(ne); c[:] = -w
    Ab = np.vstack([Aub, -np.eye(ne)]); bb = np.hstack([bub, -1e-9 * np.ones(ne)])
    rr = linprog(c, A_ub=Ab, b_ub=bb, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * ne, method="highs")
    if rr.status != 0:
        continue
    s = int((rr.x > 1e-12).sum())
    if s > bs:
        bs = s; best = rr.x
alpha = [mp.mpf(float(x)) for x in best]
alpha = alpha  # normalised by sum = 1 already
W("== n14 curvature (correct gap parameterisation) ==")
W("KKT stress support: %d of %d ; sum alpha = %s" % (bs, ne, mp.nstr(sum(alpha), 12)))

GAP0 = [SWr[k + 1] - SWr[k] for k in range(9)]
D0v = GAP0[:]
W("free gap vector (deg): %s" % [mp.nstr(x * 180 / mp.pi, 10) for x in D0v])

def angles(D):
    tD = sum(D); D0 = 2 * mp.pi - tD
    gaps = [D0] + list(D)
    th = []; acc = mp.mpf(0)
    for k in range(10):
        acc += gaps[k]; th.append(acc - gaps[0])   # gauge: theta_0 = 0
    return th

def energy(D, alpha=alpha):
    th = angles(D)
    AP = [(mp.cos(t), mp.sin(t)) for t in th]
    idx = {j: 2 * i for i, j in enumerate(free_sites)}
    nv = 2 * len(free_sites)
    Hm = [[mp.mpf(0)] * nv for _ in range(nv)]; lin = [mp.mpf(0)] * nv; const = mp.mpf(0)
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

# sanity: angles at D_base must reproduce the switch angles up to a rotation
th = angles(D0v)
W("angle check: max |th_k - (SWr_k - SWr_0)| = %s" % max(abs(th[k] - (SWr[k] - SWr[0])) for k in range(10)))
E0 = energy(D0v)
W("E(D_base) = %s ; r*^2 = %s ; difference = %s" % (mp.nstr(E0, 25), mp.nstr(r * r, 25), mp.nstr(E0 - r * r, 6)))
h1 = mp.mpf("1e-18"); h2 = mp.mpf("1e-12")
gr = []
for k in range(9):
    Dp = list(D0v); Dm = list(D0v); Dp[k] += h1; Dm[k] -= h1
    gr.append((energy(Dp) - energy(Dm)) / (2 * h1))
W("gradient dE/dD_k = %s" % [mp.nstr(x, 8) for x in gr])
H = [[mp.mpf(0)] * 9 for _ in range(9)]
for k in range(9):
    for l in range(k, 9):
        acc = mp.mpf(0); ok = True
        for sk in (1, -1):
            for sl in (1, -1):
                Dp = list(D0v); Dp[k] += sk * h2; Dp[l] += sl * h2
                vv = energy(Dp)
                if vv is None:
                    ok = False; break
                acc += sk * sl * vv
            if not ok:
                break
        H[k][l] = H[l][k] = (acc / (4 * h2 * h2)) if ok else None
if all(H[i][j] is not None for i in range(9) for j in range(9)):
    Hn = np.array([[float(H[i][j]) for j in range(9)] for i in range(9)])
    W("Hessian eigenvalues (9 free gaps): %s" % ["%.6e" % x for x in np.linalg.eigvalsh(Hn)])
    sel = [k for k in range(9) if k not in [4, 9]]
    evc = np.linalg.eigvalsh(Hn[np.ix_(sel, sel)])
    W("critical-cone eigenvalues (gaps 4,9 at cap, fixed): %s" % ["%.6e" % x for x in evc])
    W("lambda_min on critical cone = %.6e -> %s" % (evc[0], "locally stable" if evc[0] > 1e-12 else ("marginal" if evc[0] > -1e-12 else "NEGATIVE")))
    W("first-order: max|dE/dD_k| over free k = %.3e" % max(abs(float(gr[k])) for k in sel))
else:
    W("some Hessian entries undefined; printing the gradient check only")
# ---- direct perturbation test: does E actually depend on D?
import copy
Dbig = list(D0v); Dbig[0] += mp.mpf("0.05")
Ebig = energy(Dbig)
W("perturbation test: E(D_base) = %s ; E(D_base + 0.05 in gap 1) = %s" % (mp.nstr(E0, 20), mp.nstr(Ebig, 20) if Ebig is not None else "None"))
# dissect the constant part
def const_part(D):
    th = angles(D); AP = [(mp.cos(t), mp.sin(t)) for t in th]
    idx = {j: 2 * i for i, j in enumerate(free_sites)}
    const = mp.mpf(0); nfree_edges = 0
    for e, (u, v) in enumerate(edges):
        a_e = alpha[e]
        def base(node):
            if node < na: return AP[node], None
            if na <= node < na + ns:
                j = node - na
                if j in idx: return None, idx[j]
                return C[j], None
            return WI[node - na - ns], None
        pu, iu = base(u); pv, iv = base(v)
        if iu is None and iv is None:
            bx = pu[0] - pv[0]; by = pu[1] - pv[1]
            const += a_e * (bx * bx + by * by)
            nfree_edges += 1
    return const, nfree_edges
cE, nfe = const_part(D0v)
W("constant (fixed-fixed) part of E = %s over %d edges" % (mp.nstr(cE, 20), nfe))
W("sum alpha * r*^2 = %s" % mp.nstr(sum(alpha) * r * r, 20))
json.dump(dict(support=bs, E0=mp.nstr(E0, 30), grad=[mp.nstr(x, 20) for x in gr],
               H=[[mp.nstr(H[i][j], 20) if H[i][j] is not None else None for j in range(9)] for i in range(9)]),
          open(HERE.parent / "evidence/n14curv.json", "w"), indent=1)
(HERE.parent / "logs/n14curv.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/n14curv.txt")


