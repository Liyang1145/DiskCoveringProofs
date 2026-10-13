"""n14faces.py -- (a) Lead-requested obtuse/barycentric diagnostic for all 14 tight faces;
(b) which edges of the 62-edge network are forced to zero by the KKT system;
(c) dimension/face structure of the feasible alpha-cone; (d) max alpha_e per edge.
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

W("== (a) triangle-type / barycentric diagnostic for the 14 tight faces ==")
W("   (a face is 'thin' when its circumcentre lies outside the triangle: barycentric coordinate < 0)")
types = []
for k, f in enumerate(FACES):
    P = [C[i] for i in f]
    u = WITS[k]
    # barycentric coordinates of u w.r.t. P
    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
    d = cross(P[0], P[1], P[2])
    l1 = cross(u, P[1], P[2]) / d
    l2 = cross(P[0], u, P[2]) / d
    l3 = cross(P[0], P[1], u) / d
    # interior angles
    def ang(i):
        a = P[(i + 1) % 3]; b = P[(i + 2) % 3]; o = P[i]
        v1 = (a[0] - o[0], a[1] - o[1]); v2 = (b[0] - o[0], b[1] - o[1])
        cs = (v1[0] * v2[0] + v1[1] * v2[1]) / (mp.sqrt(v1[0] ** 2 + v1[1] ** 2) * mp.sqrt(v2[0] ** 2 + v2[1] ** 2))
        return mp.acos(cs) * 180 / mp.pi
    A3 = [ang(0), ang(1), ang(2)]
    kind = "OBTUSE" if max(A3) > 90 else ("right" if abs(max(A3) - 90) < mp.mpf("1e-9") else "acute")
    types.append(kind)
    W("   face %2d %-14s angles(deg)=%s  circ-CENTRE-in-triangle=%s  %s" % (
        k, str(f), [mp.nstr(x, 8) for x in A3], all(x >= -mp.mpf("1e-30") for x in (l1, l2, l3)), kind))
W("   counts: %s" % {t: types.count(t) for t in set(types)})

# ---------------- network
na, ns, nw = len(anchors), len(C), len(WITS)
edges = []
for i, ss in enumerate(owners):
    for s in ss:
        edges.append((i, na + s))
for k, f in enumerate(FACES):
    for s in f:
        edges.append((na + ns + k, na + s))
ne = len(edges)
Z = list(anchors) + list(C) + list(WITS)
dirs = []
for (u, v) in edges:
    dv = (Z[v][0] - Z[u][0], Z[v][1] - Z[u][1]); n_ = mp.sqrt(dv[0] ** 2 + dv[1] ** 2)
    dirs.append((dv[0] / n_, dv[1] / n_))
A = np.zeros((2 * ns, ne)); G = np.zeros((na, ne))
for e, (u, v) in enumerate(edges):
    dx, dy = float(dirs[e][0]), float(dirs[e][1])
    for node, sgn in ((u, -1.0), (v, +1.0)):
        if na <= node < na + ns:
            rr = node - na
            A[2 * rr, e] += sgn * dx; A[2 * rr + 1, e] += sgn * dy
for e, (u, v) in enumerate(edges):
    d = dirs[e]
    for node in (u, v):
        if node < na:
            a = anchors[node]; t = (-a[1], a[0])
            G[node, e] += 2 * float(d[0] * t[0] + d[1] * t[1])
for k in range(na):
    G[k, :] = G[k + 1:, :].sum(0) if k + 1 < na else 0.0

I = [0, 1, 2, 3, 5, 6, 7, 8]; AC = [4, 9]
from scipy.optimize import linprog

W("")
W("== (b) per-edge maximum alpha_e subject to the KKT system (alpha>=0, sum alpha=1) ==")
Aeq = np.zeros((2 * ns + len(I) + 1, ne + 1))
Aeq[:2 * ns, :ne] = A
for kk, k in enumerate(I):
    Aeq[2 * ns + kk, :ne] = G[k, :]; Aeq[2 * ns + kk, ne] = -1.0
Aeq[-1, :ne] = 1.0
beq = np.zeros(2 * ns + len(I) + 1); beq[-1] = 1.0
Aub = np.zeros((len(AC) + ne, ne + 1))
for kk, k in enumerate(AC):
    Aub[kk, :ne] = G[k, :]; Aub[kk, ne] = -1.0
Aub[len(AC):, :ne] = -np.eye(ne)
bub = np.zeros(len(AC) + ne)
mx = np.zeros(ne); feas = []
for e in range(ne):
    c = np.zeros(ne + 1); c[e] = -1.0
    rr = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
                 bounds=[(0, None)] * ne + [(None, None)], method="highs")
    mx[e] = -rr.fun if rr.status == 0 else 0.0
    feas.append(rr.status == 0)
forced = [e for e in range(ne) if mx[e] < 1e-11]
posit = [e for e in range(ne) if mx[e] >= 1e-11]
W("   forced-zero edges: %d %s" % (len(forced), forced))
W("   positive-capable edges: %d" % len(posit))
W("   forced-zero edge types: anchor-site %d, witness-site %d" % (
    sum(1 for e in forced if e < 2 * na), sum(1 for e in forced if e >= 2 * na)))
ftri = sorted({FACES[(e - 2 * na) // 3] for e in forced if e >= 2 * na})
W("   faces containing >=1 forced-zero edge: %s" % [list(t) for t in ftri])
W("   per-edge max alpha: %s" % [("%d:%.4f" % (e, mx[e])) for e in range(ne)])

json.dump(dict(face_types=types, forced=forced, positive=posit,
               max_alpha=[float(x) for x in mx],
               faces=[list(f) for f in FACES]),
          open(HERE.parent / "evidence/n14faces.json", "w"), indent=1)
(HERE.parent / "logs/n14faces.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/n14faces.txt")
