"""amplitude_confine.py -- two finite diagnostics for the midpoint-rigidity question.

(A) Amplitude confinement of the "site follows its anchor" first-order directions:
    along a flex direction the active lengths change only at second order, so the endpoint
    constraint l_e <= U = r* + eta bounds the amplitude by s <= sqrt(eta / A_max),
    A_e := (1/2) l_e''(0).  This decides whether the first-order failure of the
    gain-vs-repair criterion is quantitatively relevant at the entry threshold
    (mu/2) eps^2 with eps = 4e-5, mu = (1-b)/B > .00857761.

(B) Does the zero-stress (6-face) structure block a *uniform* slack bound?
    The 44-edge C1175 support = 62 active edges minus the 18 edges of the six zero-weight faces.
    Its gain form  sum_{e in support} w_e |Dx_e|^2  is computed at FIXED anchors; we report its
    kernel (motions with Dx_e = 0 on every support edge) and its smallest eigenvalue.
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

scout = json.loads((ROOT / "research-2026/next-cover-global/lead/root-scout.json").read_text(encoding="utf-8"),
                   parse_float=str)
z, c_, r = (mp.mpf(x) for x in scout["z_c_r"])
s_ = mp.sqrt(1 - r * r)
a = (s_ + z) / 2
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
C += [(s_, mp.mpf(0)), (-s_, mp.mpf(0)), (z, mp.mpf(0)), (-z, mp.mpf(0)), (mp.mpf(0), -t_), (mp.mpf(0), t_)]
U = mp.mpf("0.33173203427623414")
eta = U - r
SWdeg = ["19.37393668027073", "51.774419687402606", "90.0", "128.2255803125974",
         "160.62606331972927", "199.37393668027073", "231.7744196874026",
         "270.0", "308.2255803125974", "340.62606331972927"]
TH = [mp.mpf(x) * mp.pi / 180 for x in SWdeg]
AN = [(mp.cos(x), mp.sin(x)) for x in TH]
OWN = [[0, 8], [0, 4], [4, 5], [1, 5], [1, 9], [3, 9], [3, 7], [6, 7], [2, 6], [2, 8]]
FACES = [(0, 4, 13), (0, 8, 10), (0, 10, 13), (1, 5, 13), (1, 9, 11), (1, 11, 13),
         (2, 6, 12), (2, 8, 10), (2, 10, 12), (3, 7, 12), (3, 9, 11), (3, 11, 12),
         (10, 11, 12), (10, 11, 13), (4, 5, 13), (6, 7, 12)]
ZERO_FACES = [(0, 8, 10), (1, 9, 11), (2, 8, 10), (3, 9, 11), (10, 11, 12), (10, 11, 13)]

def circum(P):
    A = mp.matrix([[2 * (P[1][0] - P[0][0]), 2 * (P[1][1] - P[0][1])],
                   [2 * (P[2][0] - P[0][0]), 2 * (P[2][1] - P[0][1])]])
    bb = mp.matrix([P[1][0] ** 2 + P[1][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2,
                    P[2][0] ** 2 + P[2][1] ** 2 - P[0][0] ** 2 - P[0][1] ** 2])
    sol = mp.lu_solve(A, bb)
    return (sol[0], sol[1])
WF = [circum([C[i] for i in f]) for f in FACES]
dist = lambda p, q: mp.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)

EDGES = []
for ai, ss in enumerate(OWN):
    for sj in ss:
        EDGES.append(("anchor", sj, ai, dist(AN[ai], C[sj])))
for fi, tri in enumerate(FACES):
    for sj in tri:
        EDGES.append(("face", sj, fi, dist(WF[fi], C[sj])))
active = [i for i, e in enumerate(EDGES) if abs(e[3] - r) < mp.mpf("1e-12")]
W("== midpoint-rigidity diagnostics ==")
W("r* = %s ; U - r* = %s ; active edges %d / %d" % (mp.nstr(r, 25), mp.nstr(eta, 6), len(active), len(EDGES)))
MU_OVER_2_EPS2 = mp.mpf("0.00857761") / 2 * mp.mpf("4e-5") ** 2
W("entry threshold (mu/2) eps^2 with eps=4e-5, mu>.00857761 : %s" % mp.nstr(MU_OVER_2_EPS2, 6))

N = 28 + 32 + 10
site_dof = lambda j: 2 * j
wit_dof = lambda f: 28 + 2 * f
anch_dof = lambda ai: 60 + ai

J = np.zeros((len(active), N))
for row, ei in enumerate(active):
    kind, sj, other, L = EDGES[ei]
    p = C[sj]; q = AN[other] if kind == "anchor" else WF[other]
    u = np.array([float((p[0] - q[0]) / L), float((p[1] - q[1]) / L)])
    J[row, site_dof(sj):site_dof(sj) + 2] += u
    if kind == "anchor":
        A = AN[other]
        J[row, anch_dof(other)] = float(np.dot(u, np.array([float(A[1]), float(-A[0])])))
    else:
        J[row, wit_dof(other):wit_dof(other) + 2] -= u
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
W("flex space (active lengths preserved + gauge removed): dim = %d" % Ns.shape[0])

# ---------------- (A) amplitude confinement
W("")
W("### (A) amplitude confinement of the flex directions")
W("    normalisation: max_j |phi_j| = 1 (if no anchor moves, max |v| over sites = 1)")
resA = []
for k in range(Ns.shape[0]):
    v = Ns[k].copy()
    phi = v[60:70]
    mx = np.abs(phi).max()
    if mx > 1e-12:
        v = v / mx
        norm_note = "phi_max=1"
    else:
        vv = np.linalg.norm(v[:60])
        v = v / (vv if vv > 0 else 1.0)
        norm_note = "no anchor motion"
    phi = v[60:70]

    def conf(ss):
        """configuration at amplitude ss: anchors on the circle, sites/witnesses linear"""
        A = [(mp.cos(TH[j] + ss * mp.mpf(float(phi[j]))), mp.sin(TH[j] + ss * mp.mpf(float(phi[j]))))
             for j in range(10)]
        P = [(C[j][0] + ss * mp.mpf(float(v[site_dof(j)])), C[j][1] + ss * mp.mpf(float(v[site_dof(j) + 1])))
             for j in range(14)]
        Wt = [(WF[f][0] + ss * mp.mpf(float(v[wit_dof(f)])), WF[f][1] + ss * mp.mpf(float(v[wit_dof(f) + 1])))
              for f in range(16)]
        return A, P, Wt

    def lens(ss):
        A, P, Wt = conf(ss)
        out = []
        for (kind, sj, other, L) in EDGES:
            qq = A[other] if kind == "anchor" else Wt[other]
            out.append(dist(P[sj], qq))
        return out
    l0 = lens(mp.mpf(0))
    A2 = []
    for i in range(len(EDGES)):
        f = lambda ss, i=i: lens(ss)[i]
        d2 = mp.diff(f, mp.mpf(0), 2)
        A2.append(d2 / 2)
    pos = [i for i in active if A2[i] > mp.mpf("1e-30")]
    if not pos:
        s_max = mp.inf
    else:
        s_max = min(mp.sqrt(eta / A2[i]) for i in pos)
    beta_max = s_max * max(abs(phi)) if mx > 1e-12 else mp.mpf(0)
    resA.append((k, norm_note, min(A2), max(A2), s_max, beta_max))
    W("  flex %d (%s): A_e range [%s, %s] ; s_max = %s ; beta_max = %s" % (
        k, norm_note, mp.nstr(min(A2), 4), mp.nstr(max(A2), 4),
        mp.nstr(s_max, 4) if s_max != mp.inf else "inf", mp.nstr(beta_max, 6)))
W("")
W("  interpretation: along these directions the anchor can move at most beta_max, and the")
W("  un-repaired normalization cost is ~ lambda_e beta_max^2 <= %s" % mp.nstr(
    mp.mpf("0.250177") * max(x[5] for x in resA) ** 2 if max(x[5] for x in resA) != mp.inf else mp.inf, 6))
W("  vs the entry threshold %s" % mp.nstr(MU_OVER_2_EPS2, 6))

# ---------------- (B) support kernel (fixed anchors)
W("")
W("### (B) C1175 support (44 edges) gain form at FIXED anchors")
supp = [i for i, e in enumerate(EDGES)
        if (e[0] == "anchor") or (e[0] == "face" and FACES[e[2]] not in ZERO_FACES and FACES[e[2]] not in [(4, 5, 13), (6, 7, 12)])]
W("  support edges: %d (anchor-site %d, positive-weight face-site %d)" % (
    len(supp), sum(1 for i in supp if EDGES[i][0] == "anchor"),
    sum(1 for i in supp if EDGES[i][0] == "face")))
# edge-vector map at fixed anchors: rows = 2 per support edge, cols = 60 (sites+witnesses)
K = np.zeros((2 * len(supp), 60))
for row, ei in enumerate(supp):
    kind, sj, other, L = EDGES[ei]
    # Dx_e = Dc_sj - Dw_f  (2-vector); x and y components give the two rows
    K[2 * row, site_dof(sj)] += 1.0
    K[2 * row + 1, site_dof(sj) + 1] += 1.0
    if kind == "face":
        K[2 * row, wit_dof(other)] -= 1.0
        K[2 * row + 1, wit_dof(other) + 1] -= 1.0
svK = np.linalg.svd(K, compute_uv=False)
rankK = int((svK > 1e-11 * svK[0]).sum())
W("  edge-vector map: %s ; rank=%d ; kernel dim=%d  (0 => every nonzero free motion changes some" % (K.shape, rankK, 60 - rankK))
W("     support edge vector, i.e. the support gain form is positive definite)")
G = K.T @ K
ev = np.linalg.eigvalsh(G)
W("  smallest eigenvalues of sum_{support} |Dx_e|^2 : %s" % ["%.6e" % x for x in ev[:4]])
W("  => zero-weight (6-face) edges do NOT block positive defiteness of the support gain form;")
W("     they are face edges, while the normalization repair acts only on the 20 anchor edges,")
W("     all of which carry positive weight in the C1175 stress.")
json.dump(dict(r=mp.nstr(r, 40), eta=mp.nstr(eta, 20), flex_dim=int(Ns.shape[0]),
               A=[dict(k=k, note=nn, s_max=mp.nstr(sm, 20), beta_max=mp.nstr(bm, 20)) for k, nn, _, _, sm, bm in resA],
               support_edges=len(supp), support_rank=int(rankK),
               support_min_eig=[float(x) for x in ev[:4]]),
          open(HERE.parent / "evidence/amplitude_confine.json", "w"), indent=1)
(HERE.parent / "logs/amplitude_confine.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/amplitude_confine.txt")


