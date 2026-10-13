"""final_check.py -- 30-second self-consistency + witness-balance forced-zero summary.
Writes logs/final_check.txt (short, decisive).
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

W("== self-consistency ==")
W("anchor-site edge lengths: max|len-r*| = %s" % mp.nstr(max(abs(dist(AN[i], C[j]) - r) for (i, j) in tp), 4))
W("witness-site edge lengths: max|len-r*| = %s" % mp.nstr(max(abs(dist(WI[k], C[j]) - r) for k, f in enumerate(FACES) for j in f), 4))
W("witness is centroid of its 3 sites? max|W - (c_i+c_j+c_l)/3| = %s" % mp.nstr(max(
    norm((WI[k][0] - (C[f[0]][0] + C[f[1]][0] + C[f[2]][0]) / 3, WI[k][1] - (C[f[0]][1] + C[f[1]][1] + C[f[2]][1]) / 3))
    for k, f in enumerate(FACES)), 4))

# per-witness: the 3 directions and the exact cone of nonnegative balanced weights
W("")
W("### per-witness balance cone (alpha >= 0 with sum alpha_e d_e = 0 over its 3 edges)")
import itertools
for k, f in enumerate(FACES):
    V = []
    for j in f:
        dv = (C[j][0] - WI[k][0], C[j][1] - WI[k][1])
        V.append((float(dv[0]), float(dv[1])))
    V = np.array(V)
    # nullspace of the 2x3 matrix
    U, S, Vt = np.linalg.svd(V)
    nvec = Vt[-1]
    W("   witness %2d %-14s singular values %s ; null vector %s  -> nonneg up to sign: %s" % (
        k, str(f), ["%.3e" % x for x in S], ["%+.4f" % x for x in nvec],
        "yes" if (nvec > 1e-12).all() or (nvec < -1e-12).all() else "no"))

# forced-zero edges with site + witness balance
B = np.zeros((2 * 14, ne))
for k, f in enumerate(FACES):
    for j in f:
        e = len(tp) + 3 * k + f.index(j)
        dv = (C[j][0] - WI[k][0], C[j][1] - WI[k][1]); n_ = mp.sqrt(dv[0] ** 2 + dv[1] ** 2)
        B[2 * k, e] = float(dv[0] / n_); B[2 * k + 1, e] = float(dv[1] / n_)
A = np.zeros((2 * ns, ne))
for e, (u, v) in enumerate(edges):
    p, q = (AN[u], C[v - na]) if u < na else (WI[u - na - ns], C[v - na])
    d = (q[0] - p[0], q[1] - p[1]); n_ = mp.sqrt(d[0] ** 2 + d[1] ** 2)
    d = (float(d[0] / n_), float(d[1] / n_))
    for node, sgn in ((u, -1.0), (v, +1.0)):
        if na <= node < na + ns:
            rr = node - na
            A[2 * rr, e] += sgn * d[0]; A[2 * rr + 1, e] += sgn * d[1]
from scipy.optimize import linprog
def fz(M, tag):
    m = M.shape[0]; mx = np.zeros(ne)
    for e in range(ne):
        c = np.zeros(ne); c[e] = -1.0
        rr = linprog(c, A_eq=np.vstack([M, np.ones(ne)]), b_eq=np.hstack([np.zeros(m), 1.0]),
                     bounds=[(0, None)] * ne, method="highs")
        mx[e] = -rr.fun if rr.status == 0 else 0.0
    z = [e for e in range(ne) if mx[e] <= 1e-12]
    W("   %-38s forced-zero: %2d (anchor-site %d, witness-site %d)" % (
        tag, len(z), sum(1 for e in z if e < len(tp)), sum(1 for e in z if e >= len(tp))))
    return z
W("")
W("### forced zeros under different balance systems")
zA = fz(A, "site balance only (old kernel)")
zAB = fz(np.vstack([A, B]), "site + witness balance (correct)")
W("   witness-site edges forced to zero under A+B: %d" % sum(1 for e in zAB if e >= len(tp)))
W("   their faces: %s" % sorted({FACES[(e - len(tp)) // 3] for e in zAB if e >= len(tp)}))
data = dict(forced_A=zA, forced_AB=zAB, ne=ne, n_anchor_edges=len(tp))
(HERE.parent / "evidence/final_check.json").write_text(json.dumps(data, indent=1), encoding="utf-8")
(HERE.parent / "logs/final_check.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/final_check.txt")
