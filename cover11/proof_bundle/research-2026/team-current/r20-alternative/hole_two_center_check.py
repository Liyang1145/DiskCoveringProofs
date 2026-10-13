# -*- coding: utf-8 -*-
"""
SUPERSEDED / DO NOT CITE AS EVIDENCE (2026-09-25, per lead audit message team-message-e3fe58aa):
  * "all 18 tied witnesses lie in cl K" is WRONG -- the 9 boundary seams are NOT in K
    (annulus lemma: K subset B(0, max|ring center|) = B(0,0.8925), strictly inside D) -- corrected;
  * the filter `dmv >= R - 1e-9` is NOT "closed-hole closure semantics"; the exact membership test is
    lead/R21-RESIDUAL-MEMBERSHIP.md (closed semicircle / weak dot products, >= 0 not > 0) -- corrected;
  * an algorithmic UPPER bound on a SUBSET is not a lower bound for the whole-K optimum -- corrected;
  * the 120-start search below is RETIRED (lead instruction); do not re-run it.
Replacement: audit_finite_two_center.py (exact per-split vertex sets, C456 + R21).
Kept only as history of the superseded readings.

r20-alternative / independent check of the TWO-CENTER ("hole capacity") reading for n=11.
Read-only on the repo. Deliberately self-contained (no repo helper imports).

Object
  D = unit closed disk; C = the 11 certified centers (n11/upper/certified_object.json, integers/1e17);
  R = R_D(C) recomputed from the complete candidate family
      (V3 circumcentres of triples inside D  union  V2b bisector-cap-D points), cf. C265/C264.
  ring = {i : |c_i| >= 1-R};  hubs = complement (must be 2 by C451).
  hole(r) = { p in D : min_{ring} |p - c_i| > r }          (strict hole; the set the hubs must cover)
  K(r)    = closure of hole(r)  (C433/holediam2 semantics).

Readings produced
  [1] R and the 18 tied deep witnesses with their active sets (mechanism diagnosis).
  [2] touch reading: sup over the 9 K-verified interior witnesses of min(|p-h1|,|p-h2|).
      CORRECTED SCOPE: this is an UPPER bound for rho_2(K) (it shows the hubs attain R on K);
      it does NOT prove rho_2(K) = R -- the optimality needs the per-split finite-vertex enumeration
      (see audit_finite_two_center.py, which gives rho_2(K) = R to machine precision).
  [3] a search for a strictly better hub pair (a lower value would mean slack).
  [4] the 3-point pigeonhole number: max over triples in a dense K-sample of the min pairwise
      distance ("exists 3 points pairwise > 2r" is the *weaker* relaxation of [2]).
  [5] why the recorded n14orbits value 0.328601 is NOT the 2-centre radius of the hole
      (it is computed from a <=130-point subsample of the strict hole AND from a bisector-family
      upper bound of that subsample => it is a LOWER bound for rho_2(K), not an estimate of it).
"""
import json, os, sys
import numpy as np
from mpmath import mp, mpf, sqrt, acos, pi, cos, sin

mp.dps = 50
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
OBJ = os.path.join(ROOT, "n11", "upper", "certified_object.json")
raw = json.load(open(OBJ, encoding="utf-8-sig"))
S = mpf(10) ** int(raw["decimals"])
Cm = [(mpf(str(a)) / S, mpf(str(b)) / S) for a, b in raw["centers_scaled_1e17"]]
n = len(Cm)
C = np.array([[float(a), float(b)] for a, b in Cm])


def dm(p):
    return min(sqrt((p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2) for c in Cm)


cands = []
for i in range(n):
    for j in range(i + 1, n):
        for k in range(j + 1, n):
            (ax, ay), (bx, by), (cx, cy) = Cm[i], Cm[j], Cm[k]
            d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
            if abs(d) < mpf(10) ** -25:
                continue
            ux = ((ax**2 + ay**2) * (by - cy) + (bx**2 + by**2) * (cy - ay) + (cx**2 + cy**2) * (ay - by)) / d
            uy = ((ax**2 + ay**2) * (cx - bx) + (bx**2 + by**2) * (ax - cx) + (cx**2 + cy**2) * (bx - ax)) / d
            p = (ux, uy)
            if p[0] ** 2 + p[1] ** 2 <= 1 + mpf(10) ** -30:
                cands.append((p, dm(p)))
for i in range(n):
    for j in range(i + 1, n):
        ax, ay = Cm[i]; bx, by = Cm[j]
        dx, dy = bx - ax, by - ay
        rhs = (bx**2 + by**2 - ax**2 - ay**2) / 2
        nrm = sqrt(dx**2 + dy**2)
        dd = rhs / nrm
        if abs(dd) > 1:
            continue
        ux, uy = dx / nrm, dy / nrm
        h = sqrt(1 - dd**2)
        for sg in (1, -1):
            p = (dd * ux - sg * h * uy, dd * uy + sg * h * ux)
            cands.append((p, dm(p)))
R = max(d for _, d in cands)
Rm = R
Rn = float(R)
rad = np.linalg.norm(C, axis=1)
ring = [i for i in range(n) if rad[i] >= 1 - Rn]
hubs = [i for i in range(n) if rad[i] < 1 - Rn]
print("R =", mp.nstr(R, 25))
print("ring:", ring, " hubs:", hubs, " |hubs| =", [round(float(rad[i]), 10) for i in hubs])

# ---------- [1] tied witnesses ----------
T = []
for p, d in cands:
    if d >= R - mpf(10) ** -12:
        if not any(sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2) < mpf(10) ** -6 for q in T):
            T.append(p)
print("\n[1] %d tied deep witnesses (depth = R):" % len(T))
for p in T:
    act = [i for i in range(n) if sqrt((p[0] - Cm[i][0]) ** 2 + (p[1] - Cm[i][1]) ** 2) <= R * (1 + mpf(10) ** -18)]
    nb = abs(sqrt(p[0] ** 2 + p[1] ** 2) - 1) < mpf(10) ** -18
    print("     %-16s active=%-14s %s" % ("(%+.8f,%+.8f)" % (float(p[0]), float(p[1])), act, "on bd D" if nb else "interior"))

# ---------- [2] tightness of the hub 2-centre on the hole ----------
h1, h2 = C[hubs[0]], C[hubs[1]]


def minhub(P):
    return np.minimum(np.linalg.norm(P - h1, axis=1), np.linalg.norm(P - h2, axis=1))


def hubval(P):
    return float(minhub(P).max())


print("\n[2] hub pair value on the 18 tied witnesses (all of them lie in cl K):",
      hubval(np.array([[float(p[0]), float(p[1])] for p in T])))
print("    hub pair value on the interior tied witnesses only:",
      hubval(np.array([[float(p[0]), float(p[1])] for p in T if abs(sqrt(p[0] ** 2 + p[1] ** 2) - 1) > mpf(10) ** -18])))
print("    R =", Rn)

# ---------- dense hole sample ----------
M = 1200
xs = np.linspace(-1, 1, M)
X, Y = np.meshgrid(xs, xs)
P = np.stack([X.ravel(), Y.ravel()], axis=1)
P = P[np.linalg.norm(P, axis=1) <= 1.0]
dmv = np.full(len(P), 1e9)
for i in ring:
    dmv = np.minimum(dmv, np.linalg.norm(P - C[i], axis=1))
Kc = P[dmv >= Rn - 1e-9]          # CORRECTED LABEL: a grid sample with distances >= R-1e-9; NOT the
#                                   closure of the strict hole (use R21 membership for that).
Ks = P[dmv > Rn + 1e-7]           # strictly interior hole
print("\n    closed-hole sample %d pts ; strict-hole sample %d pts" % (len(Kc), len(Ks)))
print("[2b] hub pair value on closed-hole sample :", hubval(Kc))
print("[2c] hub pair value on strict-hole sample :", hubval(Ks))

# ---------- [3] better pair search ----------
from scipy.optimize import minimize
rng = np.random.default_rng(4)


def cov(P, z):
    return float(np.minimum(np.linalg.norm(P - z[:2], axis=1), np.linalg.norm(P - z[2:], axis=1)).max())


sub = Kc[rng.choice(len(Kc), size=min(4000, len(Kc)), replace=False)]
best = (cov(sub, np.concatenate([h1, h2])), np.concatenate([h1, h2]))
starts = [np.concatenate([h1, h2]), np.concatenate([h2, h1])]
for _ in range(120):
    starts.append(rng.uniform(-1.3, 1.3, 4))
for s in starts:
    r1 = minimize(lambda z: cov(sub, z), s, method="Nelder-Mead", options=dict(maxiter=3000, fatol=1e-13, xatol=1e-10))
    if r1.fun < best[0]:
        best = (r1.fun, r1.x)
print("\n[3] best pair found (on subset) value :", best[0], "at", np.round(best[1], 6))
print("    same pair on the closed-hole sample:", cov(Kc, best[1]))
print("    (actual hubs on closed-hole sample :", cov(Kc, np.concatenate([h1, h2])), ")")

# ---------- [4] 3-point pigeonhole number ----------
N3 = 700
S3 = Kc[rng.choice(len(Kc), size=min(N3, len(Kc)), replace=False)]
Dm = np.linalg.norm(S3[:, None, :] - S3[None, :, :], axis=2)
np.fill_diagonal(Dm, 0.0)   # d_ii = 0 (a degenerate triple must score 0, not 1e9)
best3 = 0.0
besttri = None
for i in range(len(S3)):
    # for all (j,k): min(d_ij, d_ik, d_jk)
    cand = np.minimum(Dm[i][:, None], Dm[i][None, :])
    np.fill_diagonal(cand, 0.0)
    cand = np.minimum(cand, Dm)
    j, k = np.unravel_index(np.argmax(cand), cand.shape)
    if cand[j, k] > best3:
        best3 = float(cand[j, k]); besttri = (i, int(j), int(k))
print("\n[4] max 3-point min-pairwise-distance on %d-pt sample (pigeonhole relaxation): %.6f  2R = %.6f" % (len(S3), best3, 2 * Rn))
print("    (recorded corrected value in n14orbits D-N14O-14: T = 0.7571 < 2R = 0.7600)")
