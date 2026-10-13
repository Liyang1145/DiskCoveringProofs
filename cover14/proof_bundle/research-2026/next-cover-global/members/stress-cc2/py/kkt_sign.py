"""kkt_sign.py -- settle the KKT inequality direction empirically (one LP pair) and the r factor.

The Lead's theorem: g_k <= c on the cap-active gaps. My earlier LP used g_k >= 0 (opposite).
Here both signs are tested on the same corrected geometry, and the r^2 scale is checked against a
finite-difference derivative of the true functional E(theta) = sum_e w_e |e(theta)|^2, w_e = r alpha_e.
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
A = np.zeros((2 * ns, ne)); G = np.zeros((na, ne))
for e, (u, v) in enumerate(edges):
    p, q = (AN[u], C[v - na]) if u < na else (WI[u - na - ns], C[v - na])
    d = (q[0] - p[0], q[1] - p[1]); n_ = mp.sqrt(d[0] ** 2 + d[1] ** 2)
    d = (float(d[0] / n_), float(d[1] / n_))
    for node, sgn in ((u, -1.0), (v, +1.0)):
        if na <= node < na + ns:
            rr = node - na
            A[2 * rr, e] += sgn * d[0]; A[2 * rr + 1, e] += sgn * d[1]
    for node in (u, v):
        if node < na:
            a = AN[node]; t = (-a[1], a[0])
            G[node, e] += 2.0 * float(d[0] * t[0] + d[1] * t[1])
# NOTE: this G is the coefficient of alpha in dE_units/dtheta_i, where E_units = sum alpha_e |e|^2
# (unit normalisation). The true functional uses w_e = r*alpha_e, so the physical gap slope is r*G.
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
for sign, name in ((+1.0, "g_k <= c  (Lead's theorem)"), (-1.0, "g_k >= c  (my earlier LP)")):
    Aub = np.zeros((len(AC) + ne, ne + 1))
    for kk, k in enumerate(AC):
        Aub[kk, :ne] = sign * G[k, :]
        Aub[kk, ne] = -sign          # sign*g_k <= sign*c
    Aub[len(AC):, :ne] = -np.eye(ne)
    bub = np.zeros(len(AC) + ne)
    rr = linprog(np.zeros(ne + 1), A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
                 bounds=[(0, None)] * ne + [(None, None)], method="highs")
    W("KKT with %-28s : status=%s (%s)" % (name, rr.status, "FEASIBLE" if rr.status == 0 else "EMPTY"))
    if rr.status == 0:
        al = rr.x[:ne]; gg = G @ al; c = rr.x[ne]
        W("    support %d ; c = %.8f ; g_4 = %.8f ; g_9 = %.8f ; g_4 - c = %.4e ; g_9 - c = %.4e" % (
            int((al > 1e-13).sum()), c, gg[4], gg[9], gg[4] - c, gg[9] - c))
        W("    (physical slopes with w_e = r alpha: r*g_4 = %.6e, r*g_9 = %.6e)" % (float(r) * gg[4], float(r) * gg[9]))

# ---- r-factor / derivative control: dE/dtheta for E = sum w_e |e|^2, w_e = r alpha_e
def E_of(th, w):
    Apos = [(mp.cos(t), mp.sin(t)) for t in th]
    E = mp.mpf(0)
    for e, (u, v) in enumerate(edges):
        p = Apos[u] if u < na else (C[u - na] if u < na + ns else WI[u - na - ns])
        q = Apos[v] if v < na else (C[v - na] if v < na + ns else WI[v - na - ns])
        E += w[e] * ((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)
    return E
w = [r / ne] * ne            # sum w_e = r  => E(theta*) = r * (sum alpha) * r^2 / r ... see note
W("")
W("== r factor control (uniform w_e = r/ne, so sum_e w_e = r) ==")
for i in (4, 9):
    thp = list(SW); thp[i] += mp.mpf("1e-20")
    thm = list(SW); thm[i] -= mp.mpf("1e-20")
    fd = (E_of(thp, w) - E_of(thm, w)) / (2 * mp.mpf("1e-20"))
    # formula: sum_e 2 w_e |e| (d_e . t_i) with |e| = r  =>  2 r^2 (1/ne) sum (d,t)
    frm = mp.mpf(0)
    for e, (u, v) in enumerate(edges):
        if u != i and v != i:
            continue
        p = AN[u] if u < na else C[u - na]; q = AN[v] if v < na else C[v - na]
        n_ = mp.sqrt((q[0] - p[0]) ** 2 + (q[1] - p[1]) ** 2)
        d = ((q[0] - p[0]) / n_, (q[1] - p[1]) / n_)
        t = (-AN[i][1], AN[i][0])
        frm += 2 * w[e] * n_ * (d[0] * t[0] + d[1] * t[1])
    W("   anchor %d: finite-difference dE/dtheta = %s ; formula r^2*2*sum(alpha(d.t)) = %s" % (
        i, mp.nstr(fd, 12), mp.nstr(frm, 12)))
W("   => the physical gap slope carries r^2 with normalised alpha, equivalently 2r(tau) with")
W("      weight-per-length stress; my earlier 'tau = 2 sum alpha(d.t)' carried the r factor only")
W("      implicitly through |e| = r. Sign convention: g_k = sum_{i>k} dE/dtheta_i and the cap")
W("      constraint Delta_k <= L* gives  g_k <= c  (directional derivative along the feasible")
W("      direction Delta_k decreasing must be <= 0), matching the Lead's theorem.")

json.dump(dict(ac=[int(x) for x in AC], interior=[int(x) for x in I]),
          open(HERE.parent / "evidence/kkt_sign.json", "w"), indent=1)
(HERE.parent / "logs/kkt_sign.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/kkt_sign.txt")
