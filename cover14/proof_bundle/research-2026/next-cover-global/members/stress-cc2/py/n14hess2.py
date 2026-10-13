"""n14hess2.py -- curvature + cone structure for the corrected n14 KKT stress.

Energy functional used: E(theta) = sum_e alpha_e * |e(theta)|^2 with
  * theta = the 9 free gap variables (gap 0 determined by sum=2pi),
  * witnesses FIXED at their candidate (empty-circle centre) positions,
  * the 4 unanchored sites FIXED at their candidate positions,
  * the 10 anchored sites left free (Dirichlet) -- reported both ways.
At the candidate E(theta*) = sum_e alpha_e * r*^2.
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
tight_pairs = [(i, j) for i in range(10) for j in range(14) if abs(dist(AN[i], C[j]) - r) < mp.mpf("1e-12")]
edges = [(i, j + na) for (i, j) in tight_pairs]
for k, f in enumerate(FACES):
    for j in f:
        edges.append((na + ns + k, na + j))
ne = len(edges)
Z = list(AN) + list(C) + list(WI)
anch_deg = {j: sum(1 for (i, jj) in tight_pairs if jj == j) for j in range(14)}
free_sites = [j for j in range(14) if anch_deg[j] > 0]
W("== n14 curvature + cone (corrected) ==")
W("anchored free sites: %s ; unanchored (held fixed): %s" % (free_sites, [j for j in range(14) if anch_deg[j] == 0]))

# ---------- alpha: use the KKT LP solution from n14v2 (recompute here)
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
rows = 2 * ns + len(I) + 1
Aeq = np.zeros((rows, ne + 1)); Aeq[:2 * ns, :ne] = A
for kk, k in enumerate(I):
    Aeq[2 * ns + kk, :ne] = G[k, :]; Aeq[2 * ns + kk, ne] = -1.0
Aeq[-1, :ne] = 1.0
beq = np.zeros(rows); beq[-1] = 1.0
Aub = np.zeros((len(AC) + ne, ne + 1))
for kk, k in enumerate(AC):
    Aub[kk, :ne] = -G[k, :]
Aub[len(AC):, :ne] = -np.eye(ne)
bub = np.zeros(len(AC) + ne)
# find the KKT point that maximises the number of strictly positive edges: maximise min alpha_e
lo, hi = 0.0, 5e-3
best = None
for _ in range(50):
    mid = 0.5 * (lo + hi)
    Ab = np.vstack([Aub, np.hstack([-np.eye(ne), np.zeros((ne, 1))])])
    bb = np.hstack([bub, -mid * np.ones(ne)])
    rr = linprog(np.zeros(ne + 1), A_ub=Ab, b_ub=bb, A_eq=Aeq, b_eq=beq,
                 bounds=[(0, None)] * ne + [(None, None)], method="highs")
    if rr.status == 0:
        lo = mid; best = rr.x
    else:
        hi = mid
W("KKT cone: max uniform edge weight t* = %.6e" % lo)
alpha = [mp.mpf(float(x)) for x in best[:ne]]
cst = mp.mpf(float(best[ne]))
sup = [e for e in range(ne) if alpha[e] > mp.mpf("1e-12")]
W("KKT stress support: %d edges (of %d) ; sum alpha = %s" % (len(sup), ne, mp.nstr(sum(alpha), 12)))

# ---------- energy in the 9 free gap coordinates (anchored sites free, others fixed)
def anchored_energy(D, alpha=alpha):
    tD = sum(D); D0 = 2 * mp.pi - tD
    gaps = [D0] + list(D)
    th = []; acc = mp.mpf(0)
    for k in range(na):
        acc += gaps[k]; th.append(acc)
    Apos = [(mp.cos(t), mp.sin(t)) for t in th]
    freeidx = {}
    for j in free_sites:
        freeidx[j] = 2 * len(freeidx)
    nv = 2 * len(free_sites)

    def coords(node):
        """returns (fixed2 or None, var2 or None)"""
        if node < na:
            return Apos[node], None
        if na <= node < na + ns:
            j = node - na
            if j in freeidx:
                return None, freeidx[j]
            return C[j], None
        return WI[node - na - ns], None

    Hm = [[mp.mpf(0)] * nv for _ in range(nv)]
    lin = [mp.mpf(0)] * nv; const = mp.mpf(0)
    for e, (u, v) in enumerate(edges):
        al = alpha[e]
        pu, iu = coords(u); pv, iv = coords(v)
        # coordinates x_i = (base) + e_{var}
        bx = (pu[0] if pu is not None else mp.mpf(0)) - (pv[0] if pv is not None else mp.mpf(0))
        by = (pu[1] if pu is not None else mp.mpf(0)) - (pv[1] if pv is not None else mp.mpf(0))
        const += al * (bx * bx + by * by)
        # coefficient contribution of each variable
        terms = []
        if iu is not None:
            terms.append((iu, mp.mpf(1))); terms.append((iu + 1, mp.mpf(1)))
        if iv is not None:
            terms.append((iv, mp.mpf(-1))); terms.append((iv + 1, mp.mpf(-1)))
        for j, sx in terms:
            base = j % 2
            lin[j] += 2 * al * (bx if base == 0 else by) * sx
        for j, sx in terms:
            basej = j % 2
            for l, sy in terms:
                basel = l % 2
                if basej == basel:
                    Hm[j][l] += al * sx * sy
    M = mp.matrix(Hm); b = mp.matrix([-x for x in lin])
    x = mp.lu_solve(M, b)
    E = const + sum(lin[j] * x[j] for j in range(nv)) + sum(x[j] * Hm[j][l] * x[l] for j in range(nv) for l in range(nv))
    return E

GAPV = [((mp.atan2(AN[(k + 1) % 10][1], AN[(k + 1) % 10][0]) - mp.atan2(AN[k][1], AN[k][0])) % (2 * mp.pi)) for k in range(10)]
D0vec = GAPV[1:]
E0 = anchored_energy(D0vec)
W("")
W("E(D_base) = %s ; sum(alpha)*r*^2 = %s ; difference = %s" % (
    mp.nstr(E0, 25), mp.nstr(sum(alpha) * r * r, 25), mp.nstr(E0 - sum(alpha) * r * r, 6)))

# gradient and Hessian by central differences
h1 = mp.mpf("1e-18"); h2 = mp.mpf("1e-12")
gr = []
for k in range(9):
    Dp = list(D0vec); Dm = list(D0vec); Dp[k] += h1; Dm[k] -= h1
    gr.append((anchored_energy(Dp) - anchored_energy(Dm)) / (2 * h1))
W("gradient dE/dD_k (free gaps 1..9) = %s" % [mp.nstr(x, 8) for x in gr])
H = [[mp.mpf(0)] * 9 for _ in range(9)]
for k in range(9):
    for l in range(k, 9):
        acc = mp.mpf(0)
        for sk in (1, -1):
            for sl in (1, -1):
                Dp = list(D0vec); Dp[k] += sk * h2; Dp[l] += sl * h2
                acc += sk * sl * anchored_energy(Dp)
        v = acc / (4 * h2 * h2)
        H[k][l] = v; H[l][k] = v
Hn = np.array([[float(H[i][j]) for j in range(9)] for i in range(9)])
W("")
W("Hessian eigenvalues (9-dim, all): %s" % ["%.6e" % x for x in np.linalg.eigvalsh(Hn)])
sel = [k for k in range(9) if k not in I]      # free directions: inactive gaps 1..3,5..8
Hc = Hn[np.ix_(sel, sel)]
evc = np.linalg.eigvalsh(Hc)
W("critical cone (active caps 4,9 fixed) dim=%d ; restricted eigenvalues: %s" % (len(sel), ["%.6e" % x for x in evc]))
W("lambda_min on critical cone = %.6e" % evc[0])
W("first-order along critical cone: max|dE/dD_k| = %.3e" % max(abs(float(gr[k])) for k in sel))
json.dump(dict(t_star=float(lo), support=sup, E0=mp.nstr(E0, 30),
               grad=[mp.nstr(x, 20) for x in gr],
               H=[[mp.nstr(H[i][j], 20) for j in range(9)] for i in range(9)],
               eig_all=[float(x) for x in np.linalg.eigvalsh(Hn)],
               eig_cone=[float(x) for x in evc], cone_idx=sel),
          open(HERE.parent / "evidence/n14hess2.json", "w"), indent=1)
(HERE.parent / "logs/n14hess2.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/n14hess2.txt")



