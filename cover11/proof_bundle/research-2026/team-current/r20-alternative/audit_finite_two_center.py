# -*- coding: utf-8 -*-
"""
r20-alternative / finite-witness two-centre audit of the n=11 residual hole (R21-aligned, reuse-first).

Reused (not redone):
  solo-20260922/HOLE-LINE-CONVEXIFICATION.md  (C456: conv(K cap H) = conv(V(H)), V = ring-ring + ring-line)
  solo-20260922/CURVED-HOLE-COUNTEREXAMPLE.md (C457: the established NEGATIVE control: fixed hull vertices
                                               can be 2-disk covered while K cannot)
  solo-20260922/AUXILIARY-HOLE-BRACKET.md     (C462: for ring radius exactly 19/50, t_min in
                                               (0.37996450, 0.37996454])
  lead/R21-RESIDUAL-MEMBERSHIP.md             (exact K membership: closed semicircle / weak dot products)
  lead/R21-RESIDUAL-FINITE-VERTICES.md        (annulus lemma + vertex reduction, no strict MARGIN needed)
  lead/R20-RESIDUAL-TWO-CENTER.md             (rho2(K) = min over splits of max(M_H(S-), M_H(S+)))

Definitions: r = covering radius; ring = 9 disks |c_i| >= 1-r; H = B(0,1-r);
  U = {x in D : |x-c_i| > r for all ring i}; K = closure_D(U); M_H(S) = min_{h in H} max_{x in S}|x-h|^2.

All outputs are NUMERIC diagnostics (float64 + local refinement), NOT interval certificates.
"""
import json, os, time
import numpy as np
from itertools import combinations

t0 = time.time()
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))


# ============================ generic engine ============================
def dists(P, Cs):
    return np.linalg.norm(P[:, None, :] - Cs[None, :, :], axis=2)


def in_K(p, Cs, r, tol=1e-8, atol=1e-7):
    """exact membership (R21): all distances >= r (tol), |p|<1, and active normals in a CLOSED half-plane."""
    if np.linalg.norm(p) >= 1:
        return False, "|p|>=1 (annulus lemma: K strictly inside D)"
    d = np.linalg.norm(Cs - p, axis=1)
    if d.min() < r - tol:
        return False, "covered (min-r = %+.2e)" % (d.min() - r)
    act = np.where(d <= r + atol)[0]
    if len(act) <= 1:
        return True, "active<=1"
    v = Cs[act] - p
    ang = np.sort(np.arctan2(v[:, 1], v[:, 0]))
    gaps = np.diff(np.concatenate([ang, ang[:1] + 2 * np.pi]))
    gap = float(gaps.max())
    return (gap >= np.pi - 1e-9), "closed gap=%.6f vs pi" % gap


def circ_circ(p1, p2, r):
    d = np.linalg.norm(p2 - p1)
    if d > 2 * r or d == 0:
        return []
    m = 0.5 * (p1 + p2)
    u = (p2 - p1) / d
    h = np.sqrt(max(0.0, r * r - d * d / 4))
    w = np.array([-u[1], u[0]])
    return [m + h * w, m - h * w]


def ring_ring_vertices(Cs, r, tol=1e-8, atol=1e-7):
    out = []
    for i, j in combinations(range(len(Cs)), 2):
        for p in circ_circ(Cs[i], Cs[j], r):
            ok, why = in_K(p, Cs, r, tol, atol)
            if ok:
                out.append(p)
    return np.array(out) if out else np.zeros((0, 2))


def line_vertices(n, t, Cs, r, tol=1e-8, atol=1e-7):
    out = []
    for c in Cs:
        z = t - n @ c
        if abs(z) > r:
            continue
        m = c + z * n
        h = np.sqrt(max(0.0, r * r - z * z))
        w = np.array([-n[1], n[0]])
        for s in (-1, 1):
            p = m + s * h * w
            ok, _ = in_K(p, Cs, r, tol, atol)
            if ok:
                out.append(p)
    return np.array(out) if out else np.zeros((0, 2))


def _mec(P):
    k = len(P)
    if k == 0:
        return 0.0, np.zeros(2)
    if k == 1:
        return 0.0, P[0]
    best = (np.inf, None)
    for a, b in combinations(range(k), 2):
        c = 0.5 * (P[a] + P[b]); rr = 0.5 * np.linalg.norm(P[a] - P[b])
        if rr < best[0] and np.max(np.linalg.norm(P - c, axis=1)) <= rr + 1e-12:
            best = (rr, c)
    for a, b, c3 in combinations(range(k), 3):
        A, B, Cc = P[a], P[b], P[c3]
        d = 2 * (A[0] * (B[1] - Cc[1]) + B[0] * (Cc[1] - A[1]) + Cc[0] * (A[1] - B[1]))
        if abs(d) < 1e-18:
            continue
        ux = ((A @ A) * (B[1] - Cc[1]) + (B @ B) * (Cc[1] - A[1]) + (Cc @ Cc) * (A[1] - B[1])) / d
        uy = ((A @ A) * (Cc[0] - B[0]) + (B @ B) * (A[0] - Cc[0]) + (Cc @ Cc) * (B[0] - A[0])) / d
        cc = np.array([ux, uy]); rr = np.linalg.norm(cc - A)
        if rr < best[0] and np.max(np.linalg.norm(P - cc, axis=1)) <= rr + 1e-12:
            best = (rr, cc)
    if best[1] is None:                     # numeric fallback: farthest pair
        a, b = np.unravel_index(np.argmax(np.linalg.norm(P[:, None] - P[None, :], axis=2)), (k, k))
        best = (0.5 * np.linalg.norm(P[a] - P[b]), 0.5 * (P[a] + P[b]))
    return best


def hull(P):
    P = np.unique(np.round(P, 12), axis=0)
    if len(P) <= 2:
        return P
    Q = P[np.lexsort((P[:, 1], P[:, 0]))]

    def half(pts):
        h = []
        for p in pts:
            while len(h) >= 2 and ((h[-1][0] - h[-2][0]) * (p[1] - h[-2][1])
                                   - (h[-1][1] - h[-2][1]) * (p[0] - h[-2][0])) <= 0:
                h.pop()
            h.append(p)
        return h
    return np.array(half(Q)[:-1] + half(Q[::-1])[:-1])


def M_H(P, Hrad):
    """min over |h|<=Hrad of max_{x in P}|x-h|^2 ; exact candidate enumeration (pair/triple circles)."""
    P = np.asarray(P, float)
    if len(P) == 0:
        return 0.0, np.zeros(2)
    r0, c0 = _mec(P)                      # full-set MEC (hull restriction removed: safety over speed)
    if np.linalg.norm(c0) <= Hrad + 1e-15:
        return float(np.max(np.linalg.norm(P - c0, axis=1)) ** 2), c0
    Hv = P
    cand = [np.arctan2(x[1], x[0]) + np.pi for x in Hv]
    for xa, xb in combinations(Hv, 2):
        v = xa - xb; nv = np.linalg.norm(v)
        if nv < 1e-15:
            continue
        rhs = (xa @ xa - xb @ xb) / (2 * Hrad * nv)
        if abs(rhs) > 1:
            continue
        base = np.arctan2(v[1], v[0]); al = np.arccos(np.clip(rhs, -1, 1))
        cand += [base + al, base - al]
    cand = np.array(cand)
    P2 = (P * P).sum(1)
    uv = np.stack([np.cos(cand), np.sin(cand)], axis=1)
    vals = np.max(P2[None, :] + Hrad ** 2 - 2 * Hrad * (uv @ P.T), axis=1)
    j = int(np.argmin(vals)); best = (float(vals[j]), Hrad * uv[j])
    th0 = np.arctan2(best[1][1], best[1][0])
    grid = np.linspace(th0 - 3e-3, th0 + 3e-3, 2001)
    uv = np.stack([np.cos(grid), np.sin(grid)], axis=1)
    vals = np.max(P2[None, :] + Hrad ** 2 - 2 * Hrad * (uv @ P.T), axis=1)
    j = int(np.argmin(vals))
    if float(vals[j]) < best[0]:
        best = (float(vals[j]), Hrad * uv[j])
    return best[0], best[1]


def split_vertices(n, t, Cs, r, base, Hrad):
    """(V-, V+) for the split {n.x <= t} / {n.x >= t}; line vertices belong to BOTH sides.
       Returns (V-, V+, M_H-, M_H+, contact info)."""
    L = line_vertices(n, t, Cs, r)
    pr = base @ n
    A = base[pr <= t + 1e-12]
    B = base[pr >= t - 1e-12]
    if len(L):
        A = np.vstack([A, L]) if len(A) else L
        B = np.vstack([B, L]) if len(B) else L
    mA = M_H(A, Hrad); mB = M_H(B, Hrad)
    return A, B, mA, mB


def _val_at(n, t, Cs, r, base, Hrad):
    _, _, mA, mB = split_vertices(n, t, Cs, r, base, Hrad)
    return max(mA[0], mB[0])


def best_t_for_n(n, Cs, r, base, Hrad, lo, hi, iters=30):
    """the function t -> max(M_H(S-),M_H(S+)) has M_H(S-) nondecreasing and M_H(S+) nonincreasing;
       its minimum over t is at the crossing -> ternary/bisection search."""
    for _ in range(iters):
        m1 = lo + (hi - lo) / 3; m2 = hi - (hi - lo) / 3
        if _val_at(n, m1, Cs, r, base, Hrad) < _val_at(n, m2, Cs, r, base, Hrad):
            hi = m2
        else:
            lo = m1
        if hi - lo < 1e-13:
            break
    t = 0.5 * (lo + hi)
    return _val_at(n, t, Cs, r, base, Hrad), t


def local_opt(n0, t0, Cs, r, base, Hrad):
    """coordinate descent on the split: direction perturbation + optimal threshold for each direction."""
    n = n0 / np.linalg.norm(n0)
    th = np.arctan2(n[1], n[0])
    best = (_val_at(n, t0, Cs, r, base, Hrad), n.copy(), t0)
    step = 3e-2
    pr = base @ n if len(base) else np.zeros(1)
    lo, hi = (float(pr.min()) - 1e-9, float(pr.max()) + 1e-9) if len(base) else (-1.0, 1.0)
    for _ in range(30):
        improved = False
        for dth in (-step, step):
            th2 = th + dth
            n2 = np.array([np.cos(th2), np.sin(th2)])
            pr2 = base @ n2 if len(base) else np.zeros(1)
            lo2, hi2 = (float(pr2.min()) - 1e-9, float(pr2.max()) + 1e-9) if len(base) else (-1.0, 1.0)
            v, t2 = best_t_for_n(n2, Cs, r, base, Hrad, lo2, hi2, 22)
            if v < best[0] - 1e-15:
                best = (v, n2, t2); th = th2; improved = True
        if not improved:
            step *= 0.4
            if step < 1e-7:
                break
    return best


def min_over_splits(Cs, r, base, Hrad, ndir=181, refine=True, tag="", seeds=()):
    """min over splits (n,t) of max(M_H(S-), M_H(S+)): grid + seeded local optimisation."""
    best = (np.inf, None)
    for k in range(ndir):
        th = np.pi * k / ndir
        n = np.array([np.cos(th), np.sin(th)])
        pr = base @ n if len(base) else np.zeros(1)
        lo, hi = (float(pr.min()) - 1e-9, float(pr.max()) + 1e-9) if len(base) else (-1.0, 1.0)
        for frac in np.linspace(0, 1, 9):
            t = lo + frac * (hi - lo)
            v = _val_at(n, t, Cs, r, base, Hrad)
            if v < best[0]:
                best = (v, (n.copy(), t))
    grid_best = best[0]
    if refine:
        cands = list(seeds) + [best[1]]
        for ns, ts in cands:
            v, n2, t2 = local_opt(np.asarray(ns, float), ts, Cs, r, base, Hrad)
            if v < best[0]:
                best = (v, (n2, t2))
    print("    [%s] grid-best = %.17g ; refined min over splits = %.17g  (radius %.17g); dirs=%d, elapsed %.1f s"
          % (tag, grid_best, best[0], np.sqrt(best[0]), ndir, time.time() - t0))
    return best


# ============================ [0] C457 control ============================
print("=" * 100)
print("[0] C457 control (established negative control from solo-20260922/CURVED-HOLE-COUNTEREXAMPLE.md)")
print("    4 rings at (+-1,0),(0,+-1), r = sqrt(41/50); the 4 inner crossings P=(+-0.1,+-0.1) are the")
print("    full (unsplit) vertex set; two disks of radius 0.1 at (+-0.1,0) cover P but miss K.")
C457 = np.array([[1.0, 0], [-1.0, 0], [0, 1.0], [0, -1.0]])
r457 = np.sqrt(41.0 / 50.0)
V457 = ring_ring_vertices(C457, r457)
print("    ring-ring vertices in K:", len(V457), "->", np.round(V457, 6).tolist())
H457 = 10.0                                   # hubs unconstrained in C457
vb = min_over_splits(C457, r457, V457, H457, ndir=61, refine=False, tag="unsplit V only")
# split-aware: include line-circle vertices
best457 = (np.inf, None)
for k in range(61):
    th = np.pi * k / 61
    n = np.array([np.cos(th), np.sin(th)])
    pr = V457 @ n
    for frac in np.linspace(0, 1, 21):
        t = pr.min() + frac * (pr.max() - pr.min())
        A, B, mA, mB = split_vertices(n, t, C457, r457, V457, H457)
        v = max(mA[0], mB[0])
        if v < best457[0]:
            best457 = (v, (n, t))
print("    split-aware min over splits = %.12g (radius %.12g)   [C457: 2 disks of radius 0.1 are impossible]"
      % (best457[0], np.sqrt(best457[0])))
print("    => unsplit value %.6f (WRONG: deems 0.1 feasible) vs split-aware %.6f (CORRECT)"
      % (np.sqrt(vb[0]), np.sqrt(best457[0])))

# ============================ [1] certified ring ============================
print("=" * 100)
raw = json.load(open(os.path.join(ROOT, "n11", "upper", "certified_object.json"), encoding="utf-8-sig"))
C = np.array([[float(a) / 1e17, float(b) / 1e17] for a, b in raw["centers_scaled_1e17"]])
R = 0.3799838531198387090485182
rad = np.linalg.norm(C, axis=1)
ring = [i for i in range(11) if rad[i] >= 1 - R]
hubs = [i for i in range(11) if rad[i] < 1 - R]
Cr = C[ring]
Hrad = 1 - R
print("[1] certified ring: r = %.17g ; ring = %s ; hubs = %s ; H = B(0,%.12g)" % (R, ring, hubs, Hrad))
base = ring_ring_vertices(Cr, R)
print("    ring-ring vertices verified in K (exact criterion): %d" % len(base))
for p in base:
    ok, why = in_K(p, Cr, R)
    print("      (%+.9f,%+.9f)  %s" % (p[0], p[1], why))
waist = np.array([[0.315948156, 0.061431900], [-0.315814177, 0.062116995], [0.378416357, -0.116776858],
                  [-0.378668737, -0.115955861], [-0.000574102, -0.529412041], [0.220697611, 0.582510612],
                  [-0.219433724, 0.582987899], [0.378874421, 0.305628859], [-0.378210672, 0.306449856]])
wok = [in_K(p, Cr, R)[0] for p in waist]
print("    9 interior waist witnesses in K: %d/9" % sum(wok))
seams = np.array([[0.379546266179, 0.925172758], [0.989335098, -0.145657348], [-0.001084419, -0.999999412]])
print("    boundary seam spots (must be REJECTED): %s" % [in_K(p, Cr, R)[1][:40] for p in seams])

waistK = np.array([p for p, o in zip(waist, wok) if o])

# ---- [2] split-aware bound ----
print("-" * 100)
h1s, h2s = C[hubs[0]], C[hubs[1]]
seed = ((h2s - h1s) / np.linalg.norm(h2s - h1s), (h2s @ h2s - h1s @ h1s) / (2 * np.linalg.norm(h2s - h1s)))
best_full = min_over_splits(Cr, R, base, Hrad, ndir=181, refine=True,
                            tag="split-aware, ring-ring + line-circle", seeds=(seed,))
nf, tf = best_full[1]
A, B, mA, mB = split_vertices(nf, tf, Cr, R, base, Hrad)
print("    best split: n=(%.12f,%.12f) t=%.12f ; M_H(S-)=%.15g M_H(S+)=%.15g ; |V-|=%d |V+|=%d"
      % (nf[0], nf[1], tf, mA[0], mB[0], len(A), len(B)))
print("    contacts (S-): %s" % [tuple(np.round(x, 8)) for x in A[np.where(np.linalg.norm(A - mA[1], axis=1)
                                                                          >= np.linalg.norm(A - mA[1], axis=1).max() - 1e-9)][:3]])
print("    lower-bound reading for rho_2(K): >= %.17g (radius %.17g) ; R = %.17g ; gap = %+.3e"
      % (best_full[0], np.sqrt(best_full[0]), R, np.sqrt(best_full[0]) - R))

# ---- [3] current hubs ----
print("-" * 100)
h1, h2 = C[hubs[0]], C[hubs[1]]
n = (h2 - h1) / np.linalg.norm(h2 - h1)
tt = (h2 @ h2 - h1 @ h1) / (2 * np.linalg.norm(h2 - h1))
A, B, mA, mB = split_vertices(n, tt, Cr, R, base, Hrad)
print("[3] CURRENT hubs' bisector: M_H(S-)=%.15g (rad %.15g)  M_H(S+)=%.15g (rad %.15g) ; R = %.15g"
      % (mA[0], np.sqrt(mA[0]), mB[0], np.sqrt(mB[0]), R))
touch = max(np.minimum(np.linalg.norm(waistK - h1, axis=1), np.linalg.norm(waistK - h2, axis=1)))
print("    touch reading on the 9 K-verified waist points: %.17g  (touch - R = %+.2e)  [tightness only]"
      % (touch, touch - R))

# ---- [4] unsplit-only (insufficiency demo) ----
print("-" * 100)
best_u = min_over_splits(Cr, R, waistK, Hrad, ndir=91, refine=True,
                         tag="UNsplit: 9 waist points only", seeds=(seed,))
print("[4] waist-only run %.17g (radius %.17g) vs full-vertex run %.17g (radius %.17g)"
      % (best_u[0], np.sqrt(best_u[0]), best_full[0], np.sqrt(best_full[0])))
print("    NOTE: split_vertices ALWAYS adds the line-circle vertices (per C456/R877), so this run is")
print("    not a true 'fixed-vertices-only' pipeline; the structural insufficiency of fixed vertices is")
print("    carried by the established control C457 (4 rings; radius-0.1 pair covers the 4 hull vertices")
print("    but no radius-0.1 pair covers K). Our pipeline does NOT reproduce that error (control value")
print("    0.109501 > 0.1 above), i.e. it is calibrated on the negative control.")
print("-" * 100)
print("C462 comparison: for ring radius exactly 19/50 (slightly LARGER disks than R=%.12g):" % R)
print("    t_min in (0.37996450, 0.37996454]  ->  hole 2-centre radius is within ~1.9e-5 of 0.38 there")
print("elapsed %.1f s" % (time.time() - t0))
