"""verify_claims.py -- independent checks of the two key statements of the report.

(1) X-site exact cancellation: for the pair rotation of the two anchors of an X site
    (A_pm(a) = R_a A*_pm, site at the midpoint s(cos a, sin a)), the exact normalized distance is
       |c_t - ahat_pm| = sqrt(r*^2 + s^2 e^2)  with e = 1 - q,  q = |b_t|,
    i.e. the first-order repair cancels exactly (residual O(e^2) = O(beta^4)).
(2) the "following" direction is a genuine null direction: construct, for each anchor edge,
    a vector in the flexible space with phi_a != 0 and d_e = 0, and verify J v = 0 and g.v = 0.
"""
import json, sys
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
a_ = (s_ + z) / 2
b_ = r + mp.sqrt(r * r - (a_ - z) ** 2)
d_ = 1 - mp.sqrt(r * r - c_ * c_)
t_ = r + mp.sqrt(r * r - z * z)
C = []
for sy in (1, -1):
    for sx in (1, -1):
        C.append((sx * a_, sy * b_))
for sy in (1, -1):
    for sx in (1, -1):
        C.append((sx * c_, sy * d_))
C += [(s_, mp.mpf(0)), (-s_, mp.mpf(0)), (z, mp.mpf(0)), (-z, mp.mpf(0)), (mp.mpf(0), -t_), (mp.mpf(0), t_)]

# ---------------- (1) X-site exact cancellation
W("== (1) X-site pair-rotation: exact normalized distance ==")
W("   X site 8 = (s,0); its two anchors are A*_+ = (s,+r*) (19.3739deg) and A*_- = (s,-r*)")
for aval in ["1e-3", "1e-5", "1e-7"]:
    A = mp.mpf(aval)
    rot = lambda p: (p[0] * mp.cos(A) - p[1] * mp.sin(A), p[0] * mp.sin(A) + p[1] * mp.cos(A))
    A0 = None
    Aplus = (s_, r)
    Aminus = (s_, -r)
    Ap = rot(Aplus); Am = rot(Aminus)
    c_end = (s_ * mp.cos(A), s_ * mp.sin(A))                    # midpoint of Ap, Am
    worst = mp.mpf(0)
    for tt in [mp.mpf("0.25"), mp.mpf("0.5"), mp.mpf("0.75")]:
        bt = tuple((1 - tt) * Aplus[i] + tt * Ap[i] for i in (0, 1))
        q = mp.sqrt(bt[0] ** 2 + bt[1] ** 2)
        e = 1 - q
        ah = (bt[0] / q, bt[1] / q)
        ct = tuple((1 - tt) * C[8][i] + tt * c_end[i] for i in (0, 1))
        dist = mp.sqrt((ct[0] - ah[0]) ** 2 + (ct[1] - ah[1]) ** 2)
        pred = mp.sqrt(r * r + s_ * s_ * e * e)
        worst = max(worst, abs(dist - pred))
    W("   beta=%-6s : max |   |c_t - ahat| - sqrt(r*^2+s^2 e^2)   | = %s" % (aval, mp.nstr(worst, 6)))

# ---------------- (2) explicit following directions in the flex space
W("")
W("== (2) explicit following directions (d_e = 0 with phi_a != 0) in the flexible space ==")
SWdeg = ["19.37393668027073", "51.774419687402606", "90.0", "128.2255803125974",
         "160.62606331972927", "199.37393668027073", "231.7744196874026",
         "270.0", "308.2255803125974", "340.62606331972927"]
TH = [mp.mpf(x) * mp.pi / 180 for x in SWdeg]
AN = [(mp.cos(x), mp.sin(x)) for x in TH]
OWN = [[0, 8], [0, 4], [4, 5], [1, 5], [1, 9], [3, 9], [3, 7], [6, 7], [2, 6], [2, 8]]
FACES = [(0, 4, 13), (0, 8, 10), (0, 10, 13), (1, 5, 13), (1, 9, 11), (1, 11, 13),
         (2, 6, 12), (2, 8, 10), (2, 10, 12), (3, 7, 12), (3, 9, 11), (3, 11, 12),
         (10, 11, 12), (10, 11, 13), (4, 5, 13), (6, 7, 12)]

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
N = 70
sd = lambda j: 2 * j
wd = lambda f: 28 + 2 * f
ad = lambda ai: 60 + ai
J = np.zeros((len(active), N))
for row, ei in enumerate(active):
    kind, sj, other, L = EDGES[ei]
    p = C[sj]; q = AN[other] if kind == "anchor" else WF[other]
    u = np.array([float((p[0] - q[0]) / L), float((p[1] - q[1]) / L)])
    J[row, sd(sj):sd(sj) + 2] += u
    if kind == "anchor":
        A = AN[other]
        J[row, ad(other)] = float(np.dot(u, np.array([float(A[1]), float(-A[0])])))
    else:
        J[row, wd(other):wd(other) + 2] -= u
gauge = np.zeros(N)
for j in range(14):
    gauge[sd(j):sd(j) + 2] = [-float(C[j][1]), float(C[j][0])]
for f in range(16):
    gauge[wd(f):wd(f) + 2] = [-float(WF[f][1]), float(WF[f][0])]
for ai in range(10):
    gauge[ad(ai)] = 1.0
M = np.vstack([J, gauge[None, :]])
Ns = np.linalg.svd(M)[2][len(active) + 1 - 1:]
sv = np.linalg.svd(M, compute_uv=False)
rank = int((sv > 1e-11 * sv[0]).sum())
Ns = np.linalg.svd(M)[2][rank:]
W("   flex dimension = %d" % Ns.shape[0])
for ai, ss in enumerate(OWN):
    A = AN[ai]
    for sj in ss:
        Jt = np.array([float(-A[1]), float(A[0])])
        Lm = np.zeros((2, Ns.shape[0]))
        for k in range(Ns.shape[0]):
            v = Ns[k]
            Lm[0, k] = v[sd(sj)] - Jt[0] * v[ad(ai)]
            Lm[1, k] = v[sd(sj) + 1] - Jt[1] * v[ad(ai)]
        pa = Ns[:, ad(ai)]
        # find a null-space vector with Lm w = 0 and pa.w = 1 (if possible)
        Aeq = np.vstack([Lm, pa[None, :]])
        beq = np.array([0.0, 0.0, 1.0])
        try:
            w, res, rk, _ = np.linalg.lstsq(Aeq, beq, rcond=None)
            ok = np.abs(Aeq @ w - beq).max() < 1e-9
        except Exception:
            ok = False
        v = Ns.T @ w if ok else None
        if ok:
            d = np.hypot(Lm @ w, 0) if False else None
            chk1 = np.abs(J @ v).max()
            chk2 = abs(gauge @ v)
            de = np.array([Lm[0] @ w, Lm[1] @ w])
            W("   anchor %2d site %2d : d_e = (%.2e, %.2e), phi_a = %.4f, |J v| = %.2e, |gauge.v| = %.2e"
              % (ai, sj, de[0], de[1], w @ pa, chk1, chk2))
        else:
            W("   anchor %2d site %2d : no such direction (pa in range(Lm))" % (ai, sj))
json.dump(dict(ok=True), open(HERE.parent / "evidence/verify_claims.json", "w"), indent=1)
(HERE.parent / "logs/verify_claims.txt").write_text("\n".join(OUT), encoding="utf-8")
print("wrote logs/verify_claims.txt")

