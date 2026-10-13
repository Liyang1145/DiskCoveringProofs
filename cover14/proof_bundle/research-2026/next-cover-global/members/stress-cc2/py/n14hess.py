"""n14hess.py -- curvature of the Dirichlet network energy on the sharp domain.

Reduced coordinates: 9 free gaps D1..D9 (D0 = 2pi - sum), anchors at theta_k = sum_{t<=k} D_t.
Energy: E = min_{sites} sum_e alpha_e * |z_u - z_v|^2   (witnesses and anchors fixed).
Gradient w.r.t. D_k must annihilate the critical cone; Hessian on the critical cone must be PSD
for a (local) sharp bound. Everything is numerical-but-high-precision; not an exact certificate.
"""
import json, sys
from pathlib import Path
import numpy as np
import mpmath as mp

mp.mp.dps = 80
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom import new_geom, centers_from, dist, norm

OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

g = new_geom(); C = centers_from(g); r = g["r"]; L = 2 * mp.asin(r)
SW0 = [mp.mpf(x) for x in ["19.37393668027073", "51.774419687402606", "90.0", "128.2255803125974",
                           "160.62606331972927", "199.37393668027073", "231.7744196874026",
                           "270.0", "308.2255803125974", "340.62606331972927"]]
th0 = [a * mp.pi / 180 for a in SW0]
anchors0 = [(mp.cos(a), mp.sin(a)) for a in th0]
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
na, ns, nw = 10, 14, 14
edges = []
for i, ss in enumerate(owners):
    for s in ss:
        edges.append((i, na + s))
for k, f in enumerate(FACES):
    for s in f:
        edges.append((na + ns + k, na + s))
ne = len(edges)

# ---------- alpha: a KKT-feasible stress (from n14faces per-edge max; recompute here)
import scipy.optimize as so
Z0 = list(anchors0) + list(C) + list(WITS)
def build_A_G(Z):
    dirs = []
    for (u, v) in edges:
        dv = (Z[v][0] - Z[u][0], Z[v][1] - Z[u][1]); n_ = mp.sqrt(dv[0] ** 2 + dv[1] ** 2)
        dirs.append((dv[0] / n_, dv[1] / n_))
    A = np.zeros((2 * ns, ne)); Gc = np.zeros((na, ne))
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
                a = Z[node]; t = (-a[1], a[0])
                Gc[node, e] += 2 * float(d[0] * t[0] + d[1] * t[1])
    for k in range(na):
        if k + 1 < na:
            Gc[k, :] = Gc[k + 1:, :].sum(0)
        else:
            Gc[k, :] = 0.0
    return A, Gc, dirs

A0, G0, dirs0 = build_A_G(Z0)
I = [0, 1, 2, 3, 5, 6, 7, 8]; AC = [4, 9]
Aeq = np.zeros((2 * ns + len(I) + 1, ne + 1))
Aeq[:2 * ns, :ne] = A0
for kk, k in enumerate(I):
    Aeq[2 * ns + kk, :ne] = G0[k, :]; Aeq[2 * ns + kk, ne] = -1.0
Aeq[-1, :ne] = 1.0
beq = np.zeros(2 * ns + len(I) + 1); beq[-1] = 1.0
Aub = np.zeros((len(AC) + ne, ne + 1))
for kk, k in enumerate(AC):
    Aub[kk, :ne] = G0[k, :]; Aub[kk, ne] = -1.0
Aub[len(AC):, :ne] = -np.eye(ne)
bub = np.zeros(len(AC) + ne)
# pick the feasible point maximising the minimum edge weight (to avoid spurious zero edges)
tmax = -1; best = None
lo = 0.0
for _ in range(60):
    mid = (lo + tmax if False else lo)  # placeholder
    break
# simple bisection on t: alpha_e >= t
lo, hi = 0.0, 0.02
for _ in range(40):
    mid = 0.5 * (lo + hi)
    Ab = np.vstack([Aub, np.hstack([-np.eye(ne), np.zeros((ne, 1))])])
    bb = np.hstack([bub, -mid * np.ones(ne)])
    rr = so.linprog(np.zeros(ne + 1), A_ub=Ab, b_ub=bb, A_eq=Aeq, b_eq=beq,
                    bounds=[(0, None)] * ne + [(None, None)], method="highs")
    if rr.status == 0:
        lo = mid; best = rr.x
    else:
        hi = mid
W("== n14 Hessian analysis ==")
W("max uniform edge weight t over the KKT system = %.6e (0 <=> no strictly positive stress)" % lo)
alpha = [mp.mpf(float(x)) for x in best[:ne]]
cst = mp.mpf(float(best[ne]))
W("chosen stress: %d nonzero of %d ; Sum alpha = %s" % (sum(1 for x in alpha if x > 1e-14), ne, mp.nstr(sum(alpha), 12)))
# exact residual check of the KKT conditions for this alpha
Zmp = list(anchors0) + list(C) + list(WITS)
def gap_mp(alpha, Z):
    dirs = []
    for (u, v) in edges:
        dv = (Z[v][0] - Z[u][0], Z[v][1] - Z[u][1]); n_ = mp.sqrt(dv[0] ** 2 + dv[1] ** 2)
        dirs.append((dv[0] / n_, dv[1] / n_))
    tau = [mp.mpf(0)] * na
    for e, (u, v) in enumerate(edges):
        d = dirs[e]
        for node in (u, v):
            if node < na:
                a = Z[node]; t = (-a[1], a[0])
                tau[node] += 2 * alpha[e] * (d[0] * t[0] + d[1] * t[1])
    gg = [mp.mpf(0)] * na
    for k in range(na):
        gg[k] = sum(tau[k + 1:])
    # equilibrium at sites
    res = []
    for rr_ in range(ns):
        fx = mp.mpf(0); fy = mp.mpf(0)
        for e, (u, v) in enumerate(edges):
            d = dirs[e]
            for node, sgn in ((u, -1), (v, 1)):
                if node == na + rr_:
                    fx += sgn * alpha[e] * d[0]; fy += sgn * alpha[e] * d[1]
        res.append(mp.sqrt(fx * fx + fy * fy))
    return gg, res
gg, res = gap_mp(alpha, Zmp)
W("hp KKT residuals: max|equilibrium|=%.3e ; g_k - c: %s" % (
    float(max(res)), [(k, mp.nstr(gg[k] - cst, 6)) for k in range(na)]))
W("active-cap multipliers mu4=%s mu9=%s (must be >=0)" % (
    mp.nstr(gg[4] - cst, 6), mp.nstr(gg[9] - cst, 6)))
W("sum tau = %s" % mp.nstr(sum([gg[0] - gg[0]]), 6))

# ---------- energy in reduced gap coordinates
def energy(D, alpha=alpha):
    """D: mp list of 9 free gaps (D1..D9); D0 = 2pi - sum. Returns E = Dirichlet-min energy."""
    tD = sum(D)
    D0 = 2 * mp.pi - tD
    gaps = [D0] + list(D)
    th = []
    acc = mp.mpf(0)
    for k in range(na):
        acc += gaps[k]
        th.append(acc)
    Z = [(mp.cos(t), mp.sin(t)) for t in th] + list(C) + list(WITS)
    nv = 2 * ns
    Hm = [[mp.mpf(0)] * nv for _ in range(nv)]
    lin = [mp.mpf(0)] * nv
    const = mp.mpf(0)
    for e, (u, v) in enumerate(edges):
        al = alpha[e]
        pu = Z[u]; pv = Z[v]
        duv = (pu[0] - pv[0], pu[1] - pv[1])
        constant_term = al * (duv[0] ** 2 + duv[1] ** 2)     # if both fixed
        cj = {}                                              # local var -> (+-1) * axis
        if na <= u < na + ns:
            j = 2 * (u - na); cj[j] = (1, 0); cj[j + 1] = (0, 1)
        if na <= v < na + ns:
            j = 2 * (v - na); cj[j] = (-1, 0); cj[j + 1] = (0, -1)
        const += constant_term
        for j, (sx, sy) in cj.items():
            # + 2 al duv . (sx,sy) t_j
            lin[j] += 2 * al * (duv[0] * sx + duv[1] * sy)
        for j, (sx, sy) in cj.items():
            for l, (tx, ty) in cj.items():
                Hm[j][l] += al * (sx * tx + sy * ty)
    # solve Hm x = -lin
    A = mp.matrix(Hm); b = mp.matrix([-x for x in lin])
    x = mp.lu_solve(A, b)
    E = const + sum(lin[j] * x[j] for j in range(nv)) + sum(
        x[j] * Hm[j][l] * x[l] for j in range(nv) for l in range(nv))
    return E

# base point
D_base = [mp.mpf(x) for x in [0.5655, 0.6671, 0.6671, 0.5655, 0.6762779682872483747629853,
                              0.5655, 0.6671, 0.6671, 0.5655]]
# NOTE: better to derive from the actual anchors
gaps0_mp = []
for k in range(10):
    a1 = th0[k]; a2 = th0[(k + 1) % 10]
    d = (a2 - a1) % (2 * mp.pi)
    gaps0_mp.append(d)
W("")
W("gap vector from the anchors (deg): %s" % [mp.nstr(x * 180 / mp.pi, 10) for x in gaps0_mp])
W("cap-active (gap == L*): %s" % [k for k in range(10) if abs(gaps0_mp[k] - L) < mp.mpf("1e-20")])
if abs(sum(gaps0_mp) - 2 * mp.pi) > mp.mpf("1e-30"):
    W("!! gap sum = %s != 2pi" % mp.nstr(sum(gaps0_mp), 20))
D_base = gaps0_mp[1:]
E0 = energy(D_base)
W("E(D_base) = %s ; r*^2 = %s ; E - r*^2 = %s" % (
    mp.nstr(E0, 25), mp.nstr(r * r, 25), mp.nstr(E0 - r * r, 6)))

# ---------- gradient and Hessian by central differences
def fd_grad(D, h=mp.mpf("1e-15")):
    gr = []
    for k in range(9):
        Dp = list(D); Dm = list(D)
        Dp[k] += h; Dm[k] -= h
        gr.append((energy(Dp) - energy(Dm)) / (2 * h))
    return gr

def fd_hess(D, h=mp.mpf("1e-12")):
    Hm = [[mp.mpf(0)] * 9 for _ in range(9)]
    for k in range(9):
        for l in range(k, 9):
            a = mp.mpf(0)
            for sk in (1, -1):
                for sl in (1, -1):
                    Dp = list(D); Dp[k] += sk * h; Dp[l] += sl * h
                    a += sk * sl * energy(Dp)
            v = a / (4 * h * h)
            Hm[k][l] = v; Hm[l][k] = v
    return Hm

gr = fd_grad(D_base)
W("")
W("gradient of E w.r.t. free gaps (should equal g_k coefficients up to sign):")
W("   %s" % [mp.nstr(x, 10) for x in gr])
W("   g (from stress) = %s" % [mp.nstr(x, 10) for x in gg])
Hs = fd_hess(D_base)
Hn = np.array([[float(Hs[i][j]) for j in range(9)] for i in range(9)])
W("")
W("Hessian (9x9) symmetric check: max asymmetry = %.3e" % np.abs(Hn - Hn.T).max())
ev = np.linalg.eigvalsh(Hn)
W("Hessian eigenvalues (unrestricted 9-dim): %s" % ["%.6e" % x for x in ev])

# critical cone: g_k = 0 for k in I ; (active caps at bound: their gap is fixed)
rows = []
for k in I:
    e = np.zeros(9); e[k] = 1.0; rows.append(e)
Ain = np.array(rows)
sv = np.linalg.svd(Ain, compute_uv=False)
W("")
W("critical cone = {d : d_k = 0 for k in I} (active caps 4,9 fixed), dim = %d" % (9 - len(I)))
sel = [k for k in range(9) if k not in I]
Hc = Hn[np.ix_(sel, sel)]
evc = np.linalg.eigvalsh(Hc)
W("restricted Hessian eigenvalues on the critical cone: %s" % ["%.6e" % x for x in evc])
W("lambda_min on critical cone = %.6e  -> %s" % (evc[0], "POSITIVE (local min on the face)" if evc[0] > 0 else "NEGATIVE (unstable direction)"))
# also: the full first-order check: E must increase for feasible directions
W("")
W("first-order check along the critical cone (must be 0): max |dE|/|d| over basis = %.3e" %
  max(abs(gr[k]) for k in sel))

json.dump(dict(t_max=float(lo), E0=mp.nstr(E0, 30), r2=mp.nstr(r * r, 30),
               grad=[mp.nstr(x, 20) for x in gr], g=[mp.nstr(x, 20) for x in gg],
               H=[[mp.nstr(Hs[i][j], 20) for j in range(9)] for i in range(9)],
               eig_all=[float(x) for x in ev], eig_cone=[float(x) for x in evc],
               cone_idx=sel), open(HERE.parent / "evidence/n14hess.json", "w"), indent=1)
(HERE.parent / "logs/n14hess.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/n14hess.txt")
