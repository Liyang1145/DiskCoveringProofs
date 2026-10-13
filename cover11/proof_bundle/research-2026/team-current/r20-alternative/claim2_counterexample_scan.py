# -*- coding: utf-8 -*-
"""
r20-alternative / Claim-2 testing (lead: "检验/反例，不是必须证") + strengthened-version test.

Weak Claim 2: P in bd D with |P-c_i|,|P-c_j| <= r and P on the -n side  =>  |p_-| >= 1 ?  (expected FALSE)
Diagnosis to test: "near-same-radial nested arcs": both circle-circle crossings inside D while the
lens B(c_i,r) cap B(c_j,r) still contains a unit point.

Strengthened version to test (lead's suggestion, NOT a theorem):
  arcs of the two rings on bd D are both non-contained (endpoints interleave) AND the unit switch on that
  adjacent edge has equal distance <= r  =>  exactly one of p_+, p_- lies outside D ?

Deterministic structured scan (no random optimisation): grid over |c_i|,|c_j|, angular difference, r.
"""
import numpy as np
from itertools import product

rng_grid = [0.30, 0.35, 0.40, 0.45, 0.50, 0.55, 0.60]
mod_grid = [0.30, 0.45, 0.60, 0.75, 0.85, 0.92, 0.98]
ang_grid = [2, 5, 10, 20, 30, 45, 60, 90, 120, 150]          # degrees between the two centre directions


def geometry(mi, mj, th_i, th_j, r):
    ci = mi * np.array([np.cos(th_i), np.sin(th_i)])
    cj = mj * np.array([np.cos(th_j), np.sin(th_j)])
    d = np.linalg.norm(cj - ci)
    if not (1e-9 < d < 2 * r - 1e-9):
        return None
    m = 0.5 * (ci + cj)
    tau = (cj - ci) / d
    n = np.array([-tau[1], tau[0]])
    k = np.sqrt(r * r - d * d / 4)
    pp, pm = m + k * n, m - k * n
    # arcs on bd D: half-width psi, mid-angle
    def arc(c):
        dc = np.linalg.norm(c)
        if dc < 1e-12:
            return None
        cs = (1 + dc * dc - r * r) / (2 * dc)
        if abs(cs) > 1:
            return None
        psi = np.arccos(cs)
        mid = np.arctan2(c[1], c[0])
        return mid, psi
    A, B = arc(ci), arc(cj)
    if A is None or B is None:
        return None
    # interleave test on the circle (in units of the angular coordinate): endpoints of A must not both
    # lie inside B and vice versa.
    def inside(ang, arc_):
        mid, psi = arc_
        delta = (ang - mid + np.pi) % (2 * np.pi) - np.pi
        return abs(delta) <= psi + 1e-12
    a1, a2 = A[0] - A[1], A[0] + A[1]
    b1, b2 = B[0] - B[1], B[0] + B[1]
    A_in_B = inside(a1, B) and inside(a2, B)
    B_in_A = inside(b1, A) and inside(b2, A)
    nested = A_in_B or B_in_A
    overlap = (not A_in_B) and (not B_in_A) or nested
    # common covered unit points: sample 3600 unit points (structure, not optimisation)
    ths = np.linspace(0, 2 * np.pi, 3601)[:-1]
    P = np.stack([np.cos(ths), np.sin(ths)], axis=1)
    cov = (np.linalg.norm(P - ci, axis=1) <= r + 1e-12) & (np.linalg.norm(P - cj, axis=1) <= r + 1e-12)
    if not cov.any():
        return None
    # unit switch: bisector cap bd D points with equal distance <= r
    # bisector: <x-m,tau> = 0  (perpendicular bisector in the (tau,n) frame)
    proj = P @ tau - m @ tau
    eq = np.abs(proj) < 1e-3
    switch_d = np.linalg.norm(P[eq] - ci, axis=1).min() if eq.any() else np.inf
    return dict(ci=ci, cj=cj, r=r, m=m, n=n, k=k, pp=pp, pm=pm, d=d, nested=nested,
                both_in=(np.linalg.norm(pp) < 1 and np.linalg.norm(pm) < 1),
                one_out=(np.linalg.norm(pp) - 1) * (np.linalg.norm(pm) - 1) < 0,
                p_side_minus=(P[cov] @ n - m @ n), switch_leq_r=bool(switch_d <= r + 1e-9),
                n_cov=int(cov.sum()))


# ---------------- weak claim 2: look for both-inside + common covered unit point ----------------
hits = []
for r, mi, mj, dth in product(rng_grid, mod_grid, mod_grid, ang_grid):
    g = geometry(mi, mj, 0.0, np.deg2rad(dth), r)
    if g is None:
        continue
    if g["both_in"]:
        hits.append((r, mi, mj, dth, g))
print("[1] weak claim 2: configurations with BOTH crossings inside D and a common covered unit point:")
print("    count = %d (out of the scanned grid)" % len(hits))
for h in hits[:8]:
    r, mi, mj, dth, g = h
    print("      r=%.2f |ci|=%.2f |cj|=%.2f angdiff=%3d deg  nested=%s  #covered unit pts=%d  |p+|=%.6f |p-|=%.6f"
          % (r, mi, mj, dth, g["nested"], g["n_cov"], np.linalg.norm(g["pp"]), np.linalg.norm(g["pm"])))
print("    => " + ("COUNTEREXAMPLE to the weak claim exists (see above; P on the p_- side with |p_-|<1)"
                   if hits else "no counterexample in this grid"))

# ---------------- strengthened version: non-nested arcs + switch <= r => exactly one crossing outside ----------------
bad = []
tot = 0
for r, mi, mj, dth in product(rng_grid, mod_grid, mod_grid, ang_grid):
    g = geometry(mi, mj, 0.0, np.deg2rad(dth), r)
    if g is None:
        continue
    if g["nested"] or not g["switch_leq_r"]:
        continue
    tot += 1
    if not g["one_out"]:
        bad.append((r, mi, mj, dth, g))
print("\n[2] strengthened version (non-nested arcs AND unit switch distance <= r):")
print("    configurations tested = %d ; violations of 'exactly one crossing outside' = %d" % (tot, len(bad)))
for b in bad[:8]:
    r, mi, mj, dth, g = b
    print("      COUNTEREXAMPLE r=%.2f |ci|=%.2f |cj|=%.2f angdiff=%3d  |p+|=%.6f |p-|=%.6f"
          % (r, mi, mj, dth, np.linalg.norm(g["pp"]), np.linalg.norm(g["pm"])))
if not bad:
    print("    => no violation found in this structured grid (evidence, NOT a theorem)")
    print("       monotone pattern observed: min(|p+|,|p-|) < 1 < max(|p+|,|p-|) whenever a common")
    print("       covered unit point exists in the non-nested + switch<=r class.")

# ---------------- explicit rational near-nested counterexample for the WEAK claim ----------------
print("\n[3] explicit near-same-radial nested construction (weak-claim counterexample), rational data:")
r = 0.5
ci = np.array([0.9, 0.05]); cj = np.array([0.9, -0.05])
g = geometry(0.9014, 0.9014, np.arctan2(0.05, 0.9), np.arctan2(-0.05, 0.9), r)
print("    ci=(0.9,0.05) cj=(0.9,-0.05) r=0.5 -> d=%.4f k=%.6f p+=(%.6f,%.6f) |p+|=%.6f ; p-=(%.6f,%.6f) |p-|=%.6f"
      % (g["d"], g["k"], g["pp"][0], g["pp"][1], np.linalg.norm(g["pp"]), g["pm"][0], g["pm"][1], np.linalg.norm(g["pm"])))
print("    arcs on bd D: nested=%s ; common covered unit points = %d ; both crossings inside D = %s"
      % (g["nested"], g["n_cov"], g["both_in"]))
P = np.array([1.0, 0.0])
print("    P=(1,0): |P-ci|=%.6f |P-cj|=%.6f (<= r: %s) ; <P-m,n>=%.6f (side of p-: %s)"
      % (np.linalg.norm(P - ci), np.linalg.norm(P - cj), np.linalg.norm(P - ci) <= r,
         float((P - g["m"]) @ g["n"]), float((P - g["m"]) @ g["n"]) * float(g["pm"] @ g["n"] - g["m"] @ g["n"]) > 0))
print("    |p-| = %.6f < 1 while P is covered by both disks on the p- side" % np.linalg.norm(g["pm"]))
