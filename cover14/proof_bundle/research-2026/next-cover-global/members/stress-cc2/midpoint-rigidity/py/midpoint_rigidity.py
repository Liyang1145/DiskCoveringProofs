"""midpoint_rigidity.py -- does the norm-uniform-convexity gain of the common Cartesian interpolation
pay for the anchor radial-normalization repair?

Exact objects (all hypotheses stated in the report):
  * candidate: 14 sites, 16 face witnesses, 10 anchors (boundary switches), 68 incidences,
    62 active (length exactly r*) and 6 inactive (the two slack faces, length rho < r*);
  * common Cartesian interpolation of sites, witnesses and anchors between the candidate and a
    feasible endpoint (r <= U), anchors then renormalized to the unit circle;
  * exact per-edge identity (parallelogram/uniform convexity):
        |x_e(t)|^2 = (1-t)|x_e*|^2 + t|x_e|^2 - t(1-t)|Dx_e|^2 ,
    and exact normalization term, for an anchor edge with anchor b_t = (1-t)A* + tA, q_t = |b_t|:
        |c_t(v) - b_t/q_t|^2 = |x_e(t)|^2 - 2(e_t/q_t)(x_e(t).b_t) + e_t^2 ,  e_t = 1-q_t.
  * first-order criterion (with r'(0)=0 along active-constraint-preserving motions):
        |d_e|^2 := |v_v - J A_a phi_a|^2  >=  lambda_e * phi_a^2 ,   lambda_e = 1 - c_v*.A_a*
    for EVERY anchor edge e=(v,a).  This script computes, per anchor edge, the minimum of
    |d_e|^2/(lambda_e phi_a^2) over the first-order feasible motions (the null space of the
    active-constraint Jacobian, gauge fixed).  Criterion satisfied iff every such ratio >= 1.
"""
import json, sys, itertools
from pathlib import Path
import numpy as np
import mpmath as mp

mp.mp.dps = 60
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
OUT = []
def W(s=""):
    OUT.append(str(s)); print(s)

# ---------------------------------------------------------------- geometry (exact strings)
scout = json.loads((ROOT / "research-2026/next-cover-global/lead/root-scout.json").read_text(encoding="utf-8"),
                   parse_float=str)
zs = scout["z_c_r"]
z, c_, r = (mp.mpf(s) for s in zs)
s = mp.sqrt(1 - r * r)
a = (s + z) / 2
b = r + mp.sqrt(r * r - (a - z) ** 2)
d = 1 - mp.sqrt(r * r - c_ * c_)
t_ = r + mp.sqrt(r * r - z * z)
C = []
for sy in (1, -1):
    for sx in (1, -1):
        C.append((sx * a, sy * b))
for sy in (1, -1):
    for sx in (1, -1):
        C.append((sx * c_, sy * d))
C += [(s, mp.mpf(0)), (-s, mp.mpf(0)), (z, mp.mpf(0)), (-z, mp.mpf(0)), (mp.mpf(0), -t_), (mp.mpf(0), t_)]
assert len(C) == 14
U = mp.mpf("0.33173203427623414")
W("== n14 candidate: first-order rigidity and the interpolation repair criterion ==")
W("r* = %s ; U - r* = %s" % (mp.nstr(r, 30), mp.nstr(U - r, 6)))

SWdeg = ["19.37393668027073", "51.774419687402606", "90.0", "128.2255803125974",
         "160.62606331972927", "199.37393668027073", "231.7744196874026",
         "270.0", "308.2255803125974", "340.62606331972927"]
AN = [(mp.cos(mp.mpf(x) * mp.pi / 180), mp.sin(mp.mpf(x) * mp.pi / 180)) for x in SWdeg]
OWN = [[0, 8], [0, 4], [4, 5], [1, 5], [1, 9], [3, 9], [3, 7], [6, 7], [2, 6], [2, 8]]

def circum(P):
    A = mp.matrix([[2 * (P[1][0] - P[0][0]), 2 * (P[1][1] - P[0][1])],
                   [2 * (P[2][0] - P[0][0]), 2 * (P[2][1] - P[0][1])]])
    bb = mp.matrix([P[1][0] ** 2 + P[1][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2,
                    P[2][0] ** 2 + P[2][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2])
    sol = mp.lu_solve(A, bb)
    return (sol[0], sol[1])

dist = lambda p, q: mp.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)

# 16 in-disk empty-circle vertices
V = []
for tri in itertools.combinations(range(14), 3):
    P0, P1, P2 = C[tri[0]], C[tri[1]], C[tri[2]]
    det = 2 * ((P1[0] - P0[0]) * (P2[1] - P0[1]) - (P1[1] - P0[1]) * (P2[0] - P0[0]))
    if det == 0:
        continue                                  # collinear triple: no circumcentre
    u = circum([P0, P1, P2])
    if mp.sqrt(u[0] ** 2 + u[1] ** 2) > 1:
        continue
    R3 = dist(u, C[tri[0]])
    if min(dist(u, C[l]) for l in range(14) if l not in tri) < R3 - mp.mpf("1e-25"):
        continue
    V.append((tri, u, R3))
TIGHT = [v for v in V if abs(v[2] - r) < mp.mpf("1e-25")]
SLACK = [v for v in V if abs(v[2] - r) >= mp.mpf("1e-25")]
W("in-D empty-circle vertices: %d (tight %d, slack %d)" % (len(V), len(TIGHT), len(SLACK)))
W("  tight triples: %s" % [tuple(v[0]) for v in TIGHT])
W("  slack triples: %s (radius %s)" % ([(tuple(v[0]), mp.nstr(v[2], 12)) for v in SLACK], mp.nstr(SLACK[0][2], 12)))
W("  r*^2 = %s ; slack^2 = %s ; slack slack r*^2-rho^2 = %s" % (
    mp.nstr(r * r, 12), mp.nstr(SLACK[0][2] ** 2, 12), mp.nstr(r * r - SLACK[0][2] ** 2, 8)))

# ---------------------------------------------------------------- edge list
WF = [v[1] for v in TIGHT] + [v[1] for v in SLACK]
TRIPLES = [tuple(v[0]) for v in TIGHT] + [tuple(v[0]) for v in SLACK]
nsite, nwit, nanch = 14, 16, 10
EDGES = []            # (kind, site, other_index, length)
for ai, ss in enumerate(OWN):
    for sj in ss:
        EDGES.append(("anchor", sj, ai, dist(AN[ai], C[sj])))
for fi, tri in enumerate(TRIPLES):
    for sj in tri:
        EDGES.append(("face", sj, fi, dist(WF[fi], C[sj])))
W("edges: %d" % len(EDGES))
lens = [e[3] for e in EDGES]
W("  length classes: %s" % sorted({mp.nstr(x, 10) for x in lens}))
active = [i for i, e in enumerate(EDGES) if abs(e[3] - r) < mp.mpf("1e-12")]
inactive = [i for i in range(len(EDGES)) if i not in active]
W("  active (length r*): %d ; inactive (slack faces): %d" % (len(active), len(inactive)))
W("  inactive are the face edges of %s" % [tuple(TRIPLES[EDGES[i][2]]) for i in inactive[:1]])

# ---------------------------------------------------------------- DOF layout
# sites: 14*2 = 28 ; witnesses: 16*2 = 32 ; anchor angles: 10 => 70 ; gauge = 1
N = 28 + 32 + 10
def site_dof(j): return 2 * j
def wit_dof(f): return 28 + 2 * f
def anch_dof(ai): return 60 + ai

def node_pos(kind, other):
    return C[other] if kind == "anchor" else None

J = np.zeros((len(active), N))
for row, ei in enumerate(active):
    kind, sj, other, L = EDGES[ei]
    p = C[sj]
    q = AN[other] if kind == "anchor" else WF[other]
    u = np.array([float((p[0] - q[0]) / L), float((p[1] - q[1]) / L)])   # unit vector site->other
    J[row, site_dof(sj):site_dof(sj) + 2] += u
    if kind == "anchor":
        A = AN[other]
        Jt = np.array([float(-A[1]), float(A[0])])                        # dA/dtheta
        # edge vector x = c - A  =>  d|x|/dtheta = u . (-dA/dtheta)
        J[row, anch_dof(other)] = float(np.dot(u, -Jt))
    else:
        J[row, wit_dof(other):wit_dof(other) + 2] -= u
# gauge row: rotation of the whole system
g = np.zeros(N)
for j in range(14):
    g[site_dof(j):site_dof(j) + 2] = [-float(C[j][1]), float(C[j][0])]
for f in range(16):
    g[wit_dof(f):wit_dof(f) + 2] = [-float(WF[f][1]), float(WF[f][0])]
for ai in range(10):
    g[anch_dof(ai)] = 1.0
M = np.vstack([J, g[None, :]])
sv = np.linalg.svd(M, compute_uv=False)
rank = int((sv > 1e-11 * sv[0]).sum())
Ns = np.linalg.svd(M)[2][rank:]
W("")
W("### first-order feasible motions (active lengths preserved, gauge fixed)")
W("  Jacobian %s ; rank=%d ; nullity=%d (gauge row included)" % (M.shape, rank, N - rank))
W("  smallest singular values: %s" % [float(x) for x in sv[-6:]])
W("  null space dimension = %d" % Ns.shape[0])

# ---------------------------------------------------------------- per-anchor-edge criterion
W("")
W("")
W("### per-anchor-edge first-order criterion: |v_v - J A_a phi_a|^2 >= lambda_e phi_a^2")
W("    ratio_e := min over first-order feasible motions of |d_e|^2/phi_a^2 ; criterion: ratio_e >= lambda_e")
W("    lambda_e = 1 - c_v*.A_a* = (1 + r*^2 - |c_v*|^2)/2")
res = []
for ai, ss in enumerate(OWN):
    A = AN[ai]
    Jt = np.array([float(-A[1]), float(A[0])])
    for sj in ss:
        lam = float((1 + r * r - (C[sj][0] ** 2 + C[sj][1] ** 2)) / 2)
        Lm = np.zeros((2, Ns.shape[0]))
        for k in range(Ns.shape[0]):
            v = Ns[k]
            Lm[0, k] = v[site_dof(sj)] - Jt[0] * v[anch_dof(ai)]
            Lm[1, k] = v[site_dof(sj) + 1] - Jt[1] * v[anch_dof(ai)]
        G = Lm.T @ Lm
        pa = Ns[:, anch_dof(ai)].copy()
        if np.linalg.norm(pa) < 1e-13:
            res.append((ai, sj, lam, None, "no feasible motion moves this anchor"))
            continue
        w_, V_ = np.linalg.eigh(G)
        tol = max(w_.max(), 1e-300) * 1e-10
        big = w_ > tol
        if not np.any(big):
            res.append((ai, sj, lam, 0.0, "G = 0 on the null space"))
            continue
        range_part = V_[:, big] @ (V_[:, big].T @ pa)
        if np.linalg.norm(pa - range_part) > 1e-9 * np.linalg.norm(pa):
            res.append((ai, sj, lam, 0.0, "phi_a != 0 with d_e = 0 feasible"))
            continue
        rho = 1.0 / float(np.dot((V_[:, big].T @ pa) / w_[big], V_[:, big].T @ pa))
        res.append((ai, sj, lam, rho, ""))
W("   anchor site  lambda_e      min |d|^2/phi_a^2   verdict   note")
viol = []
for ai, sj, lam, rho, note in res:
    if rho is None:
        W("     %2d    %2d    %.9f   %-16s  ok      %s" % (ai, sj, lam, "-", note))
    else:
        ok = rho >= lam
        if not ok:
            viol.append((ai, sj, lam, rho))
        W("     %2d    %2d    %.9f   %.9f        %s     %s" % (ai, sj, lam, rho, "ok" if ok else "FAIL", note))
W("")
W("   criterion holds for all 20 anchor edges: %s" % (len(viol) == 0))
W("   violations: %s" % [("a%d/s%d" % (ai, sj), "rho=%.6f" % rho, "lam=%.6f" % lam, "rho/lam=%.4f" % (rho / lam)) for ai, sj, lam, rho in viol])
W("### radial rate check: the null directions preserve all active lengths, so dr/ds = 0")
r1 = np.zeros(len(active))
W("   max |J v| over the null basis = %.3e (0 means the active lengths are preserved)"
  % float(np.abs(J @ Ns.T).max()))

json.dump(dict(r=mp.nstr(r, 40), U=mp.nstr(U, 30), n_active=len(active), n_inactive=len(inactive),
               nullity=int(Ns.shape[0]), rank=int(rank),
               ratios=[dict(anchor=int(ai), site=int(sj), lam=mp.nstr(mp.mpf(lam), 20),
                            ratio=(None if rt is None else float(rt))) for ai, sj, lam, rt, _ in res],
               tight_triples=[list(v[0]) for v in TIGHT], slack_triples=[list(v[0]) for v in SLACK],
               lambda_by_site={str(j): mp.nstr((1 + r * r - (C[j][0] ** 2 + C[j][1] ** 2)) / 2, 20) for j in range(14)}),
          open(HERE.parent / "evidence/midpoint_rigidity.json", "w"), indent=1)
(HERE.parent / "logs/midpoint_rigidity.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/midpoint_rigidity.txt")

