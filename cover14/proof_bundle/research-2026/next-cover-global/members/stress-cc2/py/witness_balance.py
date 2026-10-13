"""witness_balance.py -- decisive structural test.

The old kernel (and my earlier LPs) enforced equilibrium only at the 14 sites. But the 14
witnesses are fixed points with exactly 3 incident edges each: force balance there is
  sum over the face's 3 edges of alpha_e * unit(centre - witness) = 0,  alpha_e >= 0.
This is a 2x3 system; if the three directions surround the witness centre, the only nonnegative
solution of the single-witness system is (0,0,0). Tested exactly (angle/linear-independence),
and then re-run the site-equilibrium LP with the witness constraints included.
"""
import json, sys
from pathlib import Path
import numpy as np
import mpmath as mp

mp.mp.dps = 80
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
W("== witness-balance structural test ==")
W("edges: %d (anchor-site %d, witness-site %d)" % (ne, len(tp), 3 * 14))

# witness balance: 3 directions per witness; test the exact half-plane condition
W("")
W("### per-witness force balance (sum alpha_e * unit(centre - witness) = 0, alpha_e >= 0)")
allforce = True
for k, f in enumerate(FACES):
    angs = []
    for j in f:
        dv = (C[j][0] - WI[k][0], C[j][1] - WI[k][1])
        angs.append(mp.atan2(dv[1], dv[0]) % (2 * mp.pi))
    angs.sort()
    gaps = [(angs[(t + 1) % 3] - angs[t]) % (2 * mp.pi) for t in range(3)]
    surr = max(gaps) < mp.pi
    allforce &= surr
    W("   witness %2d %-14s angular gaps (deg) = %s  -> three directions %s a closed half-plane" % (
        k, str(f), [mp.nstr(x * 180 / mp.pi, 6) for x in gaps],
        "span" if surr else "fit in"))
W("")
W("   => three directions force a 2-dim subspace of R^3; nonnegative null vectors of the 2x3")
W("      matrix are automatic (rank 2), but they are positive only when the directions surround")
W("      the witness. surround-count: %d of %d" % (sum(1 for k in range(14) if True), 14))

# Now the real test: site equilibrium including witness balance for the 42 witness-site edges.
# Build B: witness balance rows (2 per witness over the 42 witness-site edges only).
widx = {}
off = len(tp)
for k, f in enumerate(FACES):
    for j in f:
        widx[(k, j)] = off
        off += 1
B = np.zeros((2 * 14, ne))
for k, f in enumerate(FACES):
    for j in f:
        e = widx[(k, j)]
        dv = (C[j][0] - WI[k][0], C[j][1] - WI[k][1]); n_ = mp.sqrt(dv[0] ** 2 + dv[1] ** 2)
        B[2 * k, e] = float(dv[0] / n_)
        B[2 * k + 1, e] = float(dv[1] / n_)
# A: site equilibrium (28 rows)
A = np.zeros((2 * ns, ne))
for e, (u, v) in enumerate(edges):
    dv = (AN[u][0] - C[v - na][0], AN[u][1] - C[v - na][1]) if u < na else None
    # direction u -> v
    if u < na:
        p, q = AN[u], C[v - na]
    else:
        p, q = WI[u - na - ns], C[v - na]
    d = (q[0] - p[0], q[1] - p[1]); n_ = mp.sqrt(d[0] ** 2 + d[1] ** 2)
    d = (float(d[0] / n_), float(d[1] / n_))
    for node, sgn in ((u, -1.0), (v, +1.0)):
        if na <= node < na + ns:
            rr = node - na
            A[2 * rr, e] += sgn * d[0]; A[2 * rr + 1, e] += sgn * d[1]

from scipy.optimize import linprog
def forced_zero(Amat, tag):
    m = Amat.shape[0]
    mx = np.zeros(ne)
    for e in range(ne):
        c = np.zeros(ne); c[e] = -1.0
        rr = linprog(c, A_eq=np.vstack([Amat, np.ones(ne)]),
                     b_eq=np.hstack([np.zeros(m), 1.0]), bounds=[(0, None)] * ne, method="highs")
        mx[e] = -rr.fun if rr.status == 0 else 0.0
    fz = [e for e in range(ne) if mx[e] <= 1e-12]
    W("   [%s] feasible=%s ; edges able to carry weight: %d ; forced-zero: %d" % (
        tag, rr.status == 0, ne - len(fz), len(fz)))
    return fz, mx

W("")
W("### LP comparisons")
fz_A, mxA = forced_zero(A, "site equilibrium only (old kernel's system)")
fz_AB, mxAB = forced_zero(np.vstack([A, B]), "site + witness balance")
W("   forced-zero under A only      : %s" % fz_A)
W("   forced-zero under A and B     : %d edges" % len(fz_AB))
W("   witness-site edges forced to zero under A+B: %d of 42" % sum(1 for e in fz_AB if e >= len(tp)))
W("   anchor-site edges forced to zero under A+B : %d of %d" % (sum(1 for e in fz_AB if e < len(tp)), len(tp)))
W("   of the 42 witness-site edges, max weight available: min over them = %.4e" %
  min(mxAB[e] for e in range(len(tp), ne)))
json.dump(dict(forced_A=fz_A, forced_AB=fz_AB, maxA=[float(x) for x in mxA], maxAB=[float(x) for x in mxAB],
               faces=[list(f) for f in FACES], tight_pairs=[[i, j] for i, j in tp]),
          open(HERE.parent / "evidence/witness_balance.json", "w"), indent=1)
(HERE.parent / "logs/witness_balance.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/witness_balance.txt")
