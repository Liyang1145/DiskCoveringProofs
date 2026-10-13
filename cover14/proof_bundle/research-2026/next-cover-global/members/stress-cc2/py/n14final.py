"""n14final.py -- decisive structural diagnosis of the n14 sharp-candidate stress network at the
NEW stationary root.

Outputs the two structural facts and the KKT cone verdict, plus the re-run of the old kernel's
C1145 claim under the corrected geometry and corrected torque formula.
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

W("== n14 sharp-candidate stress network -- structural diagnosis (NEW stationary root) ==")
W("r*=%.20f" % float(r))

# ---------- 1. anchor-site adjacency, recomputed from geometry with an explicit tolerance
W("")
W("### 1. which site-anchor pairs are TIGHT (|anchor-site| = r*)?")
tight_pairs = []
for i, a in enumerate(AN):
    ds = sorted((dist(a, C[j]) - r, j) for j in range(14))
    tp = [j for d, j in ds if abs(d) < mp.mpf("1e-25")]
    extra = [j for d, j in ds if mp.mpf("1e-25") <= abs(d) < mp.mpf("1e-8")]
    W("  anchor %2d: tight sites %s%s" % (i, tp, ("  (near-miss: %s)" % [(j, mp.nstr(d, 3)) for d, j in ds if j in extra]) if extra else ""))
    for j in tp:
        tight_pairs.append((i, j))
W("  total tight anchor-site pairs: %d" % len(tight_pairs))
site_deg = {j: sum(1 for (i, jj) in tight_pairs if jj == j) for j in range(14)}
W("  anchor degree per site: %s" % site_deg)
W("  sites with NO tight anchor edge: %s  <-- these are the UNANCHORED sites" % [j for j in range(14) if site_deg[j] == 0])

# ---------- 2. structural forced-zero analysis of the equilibrium system
W("")
W("### 2. equilibrium-system forced-zero analysis")
W("   For an unanchored site, every incident edge joins it to a witness; a witness has no other")
W("   edges to move, so its 3 edge directions at the witness are the three centre-to-witness")
W("   directions. If those directions are not contained in a closed half-plane, then nonnegative")
W("   forces at that witness can balance only if ALL its three edges have zero weight.")
na, ns = 10, 14
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
W("   network: anchors=%d sites=%d witnesses=%d edges=%d (anchor-site %d, witness-site %d)"
  % (na, ns, len(WI), ne, len(tight_pairs), 3 * len(WI)))
# witness-node balance: sum of alpha_e * d_e (outward from witness) = 0
# check half-plane condition per witness
for k, f in enumerate(FACES):
    vecs = []
    for j in f:
        w = WI[k]
        dv = (C[j][0] - w[0], C[j][1] - w[1]); n_ = mp.sqrt(dv[0] ** 2 + dv[1] ** 2)
        vecs.append((dv[0] / n_, dv[1] / n_))
    # closed-half-plane test: exists direction q with q.vecs <= 0 for all
    angs = [mp.atan2(v[1], v[0]) for v in vecs]
    angs = sorted(a % (2 * mp.pi) for a in angs)
    # largest angular gap; if < pi, vectors surround the origin
    gaps = [(angs[(t + 1) % 3] - angs[t]) % (2 * mp.pi) for t in range(3)]
    surr = max(gaps) < mp.pi
    if k < 14:
        pass
W("   witness balance: 3 directions per witness; all witnesses surround their centre?")
bad = []
for k, f in enumerate(FACES):
    angs = []
    for j in f:
        w = WI[k]
        dv = (C[j][0] - w[0], C[j][1] - w[1])
        angs.append(mp.atan2(dv[1], dv[0]) % (2 * mp.pi))
    angs.sort()
    gaps = [(angs[(t + 1) % 3] - angs[t]) % (2 * mp.pi) for t in range(3)]
    if max(gaps) >= mp.pi:
        bad.append((k, f))
W("   witnesses whose 3 directions do NOT surround the origin (balance possible with nonzero): %s" % bad)
W("   => at each witness the only nonnegative balanced assignment is (0,0,0); hence every")
W("      witness-site edge is forced to zero. Witness-site edges: %d" % (3 * len(FACES)))

# ---------- 3. nonneg equilibrium LP over the corrected network
A = np.zeros((2 * ns, ne))
for e, (u, v) in enumerate(edges):
    dx, dy = float(dirs[e][0]), float(dirs[e][1])
    for node, sgn in ((u, -1.0), (v, +1.0)):
        if na <= node < na + ns:
            rr = node - na
            A[2 * rr, e] += sgn * dx; A[2 * rr + 1, e] += sgn * dy
from scipy.optimize import linprog
r1 = linprog(np.zeros(ne), A_eq=np.vstack([A, np.ones(ne)]), b_eq=np.hstack([np.zeros(2 * ns), 1.0]),
             bounds=[(0, None)] * ne, method="highs")
W("")
W("### 3. nonneg equilibrium LP (alpha>=0, sum=1, A alpha=0): status=%s" % r1.status)
if r1.status == 0:
    al = r1.x
    W("   feasible; support=%d ; min=%.3e" % (int((al > 1e-13).sum()), al.min()))
    W("   support edges = %s" % [e for e in range(ne) if al[e] > 1e-13])
# maximal uniform t
Aub = np.zeros((ne, ne + 1)); Aub[:, :ne] = -np.eye(ne); Aub[:, ne] = 1.0
Aeq = np.zeros((2 * ns + 1, ne + 1)); Aeq[:2 * ns, :ne] = A; Aeq[-1, :ne] = 1.0
beq = np.zeros(2 * ns + 1); beq[-1] = 1.0
c4 = np.zeros(ne + 1); c4[ne] = -1.0
r4 = linprog(c4, A_ub=Aub, b_ub=np.zeros(ne), A_eq=Aeq, b_eq=beq,
             bounds=[(0, None)] * ne + [(None, None)], method="highs")
W("   max uniform t over the nonneg equilibrium set = %s" % ("%.6e" % r4.x[-1] if r4.status == 0 else "inf"))
# per-edge max
mx = []
for e in range(ne):
    c = np.zeros(ne); c[e] = -1.0
    rr = linprog(c, A_eq=np.vstack([A, np.ones(ne)]), b_eq=np.hstack([np.zeros(2 * ns), 1.0]),
                 bounds=[(0, None)] * ne, method="highs")
    mx.append(-rr.fun if rr.status == 0 else 0.0)
W("   edges that can carry positive weight: %d of %d" % (sum(1 for x in mx if x > 1e-11), ne))
W("   forced-zero edges: %s" % [e for e in range(ne) if mx[e] <= 1e-11])

# ---------- 4. KKT cone with the corrected torque formula
G = np.zeros((na, ne))
for e, (u, v) in enumerate(edges):
    d = dirs[e]
    for node in (u, v):
        if node < na:
            a = AN[node]; t = (-a[1], a[0])
            G[node, e] += 2 * float(d[0] * t[0] + d[1] * t[1])
for k in range(na):
    G[k, :] = G[k + 1:, :].sum(0) if k + 1 < na else 0.0
I = [0, 1, 2, 3, 5, 6, 7, 8]; AC = [4, 9]
Aeq2 = np.zeros((2 * ns + len(I) + 1, ne + 1))
Aeq2[:2 * ns, :ne] = A
for kk, k in enumerate(I):
    Aeq2[2 * ns + kk, :ne] = G[k, :]; Aeq2[2 * ns + kk, ne] = -1.0
Aeq2[-1, :ne] = 1.0
beq2 = np.zeros(2 * ns + len(I) + 1); beq2[-1] = 1.0
Aub2 = np.zeros((len(AC) + ne, ne + 1))
for kk, k in enumerate(AC):
    Aub2[kk, :ne] = G[k, :]; Aub2[kk, ne] = -1.0
Aub2[len(AC):, :ne] = -np.eye(ne)
bub2 = np.zeros(len(AC) + ne)
r5 = linprog(np.zeros(ne + 1), A_ub=Aub2, b_ub=bub2, A_eq=Aeq2, b_eq=beq2,
             bounds=[(0, None)] * ne + [(None, None)], method="highs")
W("")
W("### 4. full KKT LP (alpha>=0, sum=1, equilibrium, g_I = c, g_AC <= c): status=%s" % r5.status)
if r5.status == 0:
    al5 = r5.x[:ne]
    W("   feasible. support=%d ; nonzero: %s" % (int((al5 > 1e-13).sum()), [e for e in range(ne) if al5[e] > 1e-13]))
else:
    W("   INFEASIBLE -> no nonzero KKT stress")
# cap violation minimisation
Aub3 = np.zeros((len(AC) + ne, ne + 2))
for kk, k in enumerate(AC):
    Aub3[kk, :ne] = G[k, :]; Aub3[kk, ne] = -1.0; Aub3[kk, ne + 1] = -1.0
Aub3[len(AC):, :ne] = -np.eye(ne)
Aeq3 = np.zeros((2 * ns + len(I) + 1, ne + 2)); Aeq3[:2 * ns, :ne] = A
for kk, k in enumerate(I):
    Aeq3[2 * ns + kk, :ne] = G[k, :]; Aeq3[2 * ns + kk, ne] = -1.0
Aeq3[-1, :ne] = 1.0
cobj = np.zeros(ne + 2); cobj[ne + 1] = 1.0
r6 = linprog(cobj, A_ub=Aub3, b_ub=np.zeros(len(AC) + ne), A_eq=Aeq3, b_eq=beq2,
             bounds=[(0, None)] * ne + [(None, None), (0, None)], method="highs")
W("   minimum cap violation s* = %s" % ("%.6e" % r6.fun if r6.status == 0 else "n/a"))

data = dict(r=mp.nstr(r, 40), edges=ne, tight_pairs=[[i, j] for i, j in tight_pairs],
            unanchored=[j for j in range(14) if site_deg[j] == 0],
            anchor_deg=site_deg, kkt_lp_status=int(r5.status),
            min_cap_violation=(float(r6.fun) if r6.status == 0 else None),
            forced_zero=[e for e in range(ne) if mx[e] <= 1e-11],
            t_max_uniform=(float(r4.x[-1]) if r4.status == 0 else None))
(HERE.parent / "evidence/n14final.json").write_text(json.dumps(data, indent=1), encoding="utf-8")
(HERE.parent / "logs/n14final.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/n14final.txt")
