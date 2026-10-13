# -*- coding: utf-8 -*-
"""hub_service_scalar.py -- calibration of the pure angle-capacity necessary condition for
q<=1 hub-degree extremes (lead task), plus the analytic exclusion verdict.

Model (lead): for hub j with |h_j| = s_j, every point of the circle dD(h_j, r) must be
covered by the other disks.  A ring disk at distance ell >= ell_min = (1-r) - s_j covers a
half-arc  beta = acos(ell/(2r))  of that circle; with N_j ring neighbours and the other hub
at distance d,
      (NEC)   N_j * beta_max(s_j) + beta_hh >= pi ,   beta_max = acos(((1-r)-s_j)/(2r)),
              beta_hh = acos(d/(2r)) if d <= 2r else 0.
This file (1) calibrates NEC on the saved q=0 object with its TRUE N_j, (2) finds the exact
s-thresholds at which NEC can exclude N_j = 2 and N_j = 3, (3) reports the refined reusable
resource bound.  Numeric + elementary algebra; no big runs.
"""
import json
import math
import os

ROOT = r"C:\Users\袁力阳\Desktop\ai4math2"
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")
S = 10 ** 17
R = 0.38
A = 1 - 2 * R          # core radius a = 0.24


def beta_max(s):
    ell = (1 - R) - s
    if ell <= 0:
        return math.pi / 2
    if ell >= 2 * R:
        return 0.0
    return math.acos(ell / (2 * R))


def beta_hh(d):
    if d > 2 * R:
        return 0.0
    return math.acos(max(-1.0, min(1.0, d / (2 * R))))


if __name__ == "__main__":
    print("=" * 78)
    print("A. calibration on the saved q=0 object (must be FEASIBLE, i.e. NEC holds)")
    print("=" * 78)
    J = json.load(open(ROOT + r"\n11\upper\certified_object.json", encoding="utf-8"))
    C = [(int(a) / S, int(b) / S) for a, b in J["centers_scaled_1e17"]]
    rho = [math.hypot(*c) for c in C]
    bnd = [i for i in range(11) if rho[i] >= 1 - R]
    hub = [i for i in range(11) if i not in bnd]
    print("  ring disks %s ; hubs %s (|h| = %s)" % (bnd, hub, [round(rho[i], 6) for i in hub]))
    h = [C[i] for i in hub]
    s = [rho[i] for i in hub]
    d = math.dist(h[0], h[1])
    bhh = beta_hh(d)
    # hub degrees from the earlier cellulation audit of the same object: k = 7 and 6,
    # hubs share an edge (d-edge count 1) => N_j = k_j - 1
    Ns = [6, 5]
    print("  d(h1,h2) = %.6f ; beta_hh = %.6f  (0 if d > 2r)" % (d, bhh))
    ok = True
    for j in range(2):
        b = beta_max(s[j]); v = Ns[j] * b + bhh
        ok &= (v >= math.pi)
        print("  hub %d: s = %.6f  N_j = %d  beta_max = %.6f  N*beta+beta_hh = %.6f >= pi ? %s"
              % (j + 1, s[j], Ns[j], b, v, v >= math.pi))
    print("  NEC feasible on the saved object:", ok)
    # crude scalar with N_j = 2,3 (what the exclusion would need)
    for n in (2, 3):
        v = n * beta_max(s[0]) + bhh
        print("  [diagnostic] same object with N=%d (not its true degree): %.6f" % (n, v))

    print()
    print("=" * 78)
    print("B. analytic: can NEC exclude N_j = 2 or 3 for admissible hubs?")
    print("=" * 78)
    print("  beta_max(s) = acos(((1-r)-s)/(2r)) is INCREASING in s  (ell shrinks as s grows)")
    print("  beta_hh <= pi/2 (max at d = 0) ; core condition (C4) gives min(s_1,s_2) <= sqrt((1-r)(3r-1)) = %.6f"
          % math.sqrt((1 - R) * (3 * R - 1)))
    for n in (2, 3):
        # NEC: n*beta_max(s) + beta_hh >= pi.  With the best possible beta_hh = pi/2 (d=0)
        # this needs beta_max(s) >= (pi - pi/2)/n = pi/(2n).
        need = math.pi / (2 * n)
        s_thr = (1 - R) - 2 * R * math.cos(need)
        print("  N=%d : with the best possible beta_hh = pi/2 (d = 0) NEC needs beta_max(s) >= %.6f"
              % (n, need))
        print("        <=> s >= %.6f   [with smaller beta_hh the threshold s is larger]"
              % s_thr)
        print("        admissible: s in [0, 1-r) = [0, %.4f), and min(s1,s2) <= %.6f"
              % (1 - R, math.sqrt((1 - R) * (3 * R - 1))))
        if s_thr < math.sqrt((1 - R) * (3 * R - 1)):
            print("        => the window s in [%.4f, %.4f] satisfies NEC => N=%d is NOT excluded"
                  % (max(0.0, s_thr), math.sqrt((1 - R) * (3 * R - 1)), n))
        else:
            print("        => no admissible s satisfies NEC => N=%d would be EXCLUDED" % n)

    print()
    print("=" * 78)
    print("C. refined reusable resource bound (why the scalar is loose)")
    print("=" * 78)
    print("  (i)  the scalar uses ell_min = (1-r)-s for EVERY neighbour: a hub-far ring disk")
    print("       gives a smaller arc, so the true arc sum is smaller than N*beta_max;")
    print("       conversely a ring disk at ell close to 2r contributes ~0 but still counts in N.")
    print("  (ii) it ignores that the SERVING ring disks also owe their outer arcs on dD:")
    print("       ring disk i has half-width t_i and radius rho(t_i), and sum_i 2 t_i >= 2 pi.")
    print("  (iii) tight version, still a necessary condition and LP-shaped:")
    print("       choose a service assignment sigma: hubs -> subsets S_j of ring disks; then")
    print("           for each j:  sum_{i in S_j} acos(min(1,|c_i-h_j|/(2r))) + beta_hh >= pi,")
    print("       with |c_i - h_j| = sqrt(rho(t_i)^2 + s_j^2 - 2 rho(t_i) s_j cos(phi_i - psi_j)),")
    print("       subject to the ledger constraints (t_i in [t0, asin r], sum_i 2 t_i >= 2 pi,")
    print("       overlap/private-part legality) and N_j = |S_j| bounded by the refined degree.")
    print("       The scalar replaces |c_i-h_j| by ell_min and drops the t_i/rho coupling,")
    print("       which is exactly the observed slack.")
    # measure the slack on the saved object
    tot_scalar = sum(Ns[j] * beta_max(s[j]) + bhh for j in range(2))
    print()
    print("  measured slack (saved object): sum_j (N_j beta_max + beta_hh) = %.6f vs 2*pi = %.6f"
          % (tot_scalar, 2 * math.pi))
    # true arcs of dD(h_j, r) covered, by direct sampling: (a) ring disks only, (b) ring
    # disks + the other hub (the model's "neighbours + other hub")
    for j in range(2):
        nj = 36000
        nr = nh = 0
        for k in range(nj):
            th = 2 * math.pi * k / nj
            p = (h[j][0] + R * math.cos(th), h[j][1] + R * math.sin(th))
            if math.hypot(*p) > 1:
                continue                    # outside D: no obligation
            covr = any(math.dist(p, C[i]) <= R for i in bnd)
            covh = math.dist(p, h[1 - j]) <= R
            if not covr:
                nr += 1
            if not (covr or covh):
                nh += 1
        print("   hub %d: points of dD(h_j,r) inside D NOT covered by RING disks alone: %d"
              % (j + 1, nr))
        print("           ... NOT covered by ring disks + other hub: %d  (model premise: 0)" % nh)
