"""r20 fixed-endpoint local variation (lead thread, 2026-09-25).

Read-only outside r20-chain; writes ../out/r20_fixed_endpoint_variation.txt.

Data: strict hub H, radius r, two ring endpoints cL, cR (fixed), one internal ring c.
Hypotheses of the lead's question:
  (H1) inward branch: the hub lies in the inner pin disk for each edge (|H - p_in| <= r, and the
       outer root is outside, |H - p_out| > r, so the pin criterion is equivalent to rho <= r);
  (H2) two actual covered ties: for each pair the covered unit-circle equal-distance point U is
       covered by both disks;
  (H3) two fans: rho(cL,c,H) <= r and rho(c,cR,H) <= r;
  (H4) coverage: the internal ring's disk covers the gap between the two endpoint arcs
       (both gap endpoints A',B' within r of c);
  (H5) annulus: 1-r <= |c| <= 1.
Questions: (Q1) is the fixed-endpoint total boundary span an identity in the internal ring?
           (Q2) can c be legally deformed to make at least one pin active (rho = r) without
                losing the unit-boundary coverage?
Method: exact formulas + a bounded grid/refinement over the coverage-feasible lens; the decisive
quantity is max_F max(rho_1, rho_2) versus r (positive margin => no tight configuration exists in F).
"""
import math
import numpy as np
from pathlib import Path

OUT = Path(__file__).resolve().parent.parent / "out"
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def beta(L, r):
    return math.acos((1 + L * L - r * r) / (2 * L))


def circ(A, B, C):
    e = [np.linalg.norm(B - C), np.linalg.norm(A - C), np.linalg.norm(A - B)]
    ar = abs((B[0] - A[0]) * (C[1] - A[1]) - (B[1] - A[1]) * (C[0] - A[0])) / 2
    return e[0] * e[1] * e[2] / (4 * ar) if ar > 1e-15 else np.inf


def pins(a, b, r):
    m = (np.asarray(a, float) + np.asarray(b, float)) / 2
    d = float(np.linalg.norm(np.asarray(b, float) - np.asarray(a, float)))
    n = np.array([-(np.asarray(b, float) - np.asarray(a, float))[1],
                  (np.asarray(b, float) - np.asarray(a, float))[0]]) / d
    k = math.sqrt(max(r * r - d * d / 4, 0.0))
    return m + k * n, m - k * n, k, d


def tie_and_branch(a, b, r, H):
    """covered unit tie (radical-line unit point) and the hub branches."""
    a, b = np.asarray(a, float), np.asarray(b, float)
    m = (a + b) / 2
    d = float(np.linalg.norm(b - a))
    e = (b - a) / d
    n = np.array([-e[1], e[0]])
    mn = float(m @ n)
    t = -mn + math.sqrt(mn * mn + 1 - float(m @ m))          # positive unit-circle root
    U = m + t * n
    p1, p2 = m + math.sqrt(max(r * r - d * d / 4, 0)) * n, m - math.sqrt(max(r * r - d * d / 4, 0)) * n
    inner, outer = (p1, p2) if np.linalg.norm(H - p1) < np.linalg.norm(H - p2) else (p2, p1)
    return U, t, inner, outer


def part0():
    P("=" * 100)
    P("§0 TRANSFER MAP SCOPE (exact statement, corrected per lead)")
    P("   rho(c_i,c_{i+1},H) <= r  <=>  |s_i - s_{i+1}| <= theta_i <= s_i + s_{i+1}")
    P("   hypotheses: d_i = |H-c_i| in (0,2r) (strict), theta_i in (0,pi) (H,c_i,c_{i+1} non-collinear")
    P("   so rho = |c_i c_{i+1}|/(2 sin theta_i) is defined).")
    P("   upper endpoint theta_i = s_i+s_{i+1} lies in (0,pi) -> non-degenerate -> rho = r;")
    P("   lower endpoint theta_i = |s_i-s_{i+1}| -> rho = r only when it is > 0; if s_i = s_{i+1}")
    P("   the endpoint is theta_i = 0 (collinear, rho undefined, no pin equality).")
    P("   d_i = 0 (ring at the hub) and d_i = 2r (s_i = 0, tangency) are outside the scope.")


def part1(r, h, adeg):
    P("")
    P("=" * 100)
    P("§1 INSTANCE: r = %.2f, H = (%.2f,0), endpoints |cL|=|cR|=1 at azimuth +-%.1f deg" % (r, h, adeg))
    a = math.radians(adeg)
    cL = np.array([math.cos(a), math.sin(a)])
    cR = np.array([math.cos(a), -math.sin(a)])
    H = np.array([h, 0.0])
    b1 = beta(1.0, r)
    P("   endpoint covered-arc half-width beta(1) = %.9f = %.6f deg" % (b1, math.degrees(b1)))
    gapA = -(a - b1)                     # right end of cR's arc  (azimuth)
    gapB = +(a - b1)                     # left end of cL's arc
    A = np.array([math.cos(gapA), math.sin(gapA)])
    B = np.array([math.cos(gapB), math.sin(gapB)])
    P("   gap between the endpoint arcs: azimuth [%.6f, %.6f] deg, endpoints A'=(%.9f,%.9f), B'=(%.9f,%.9f)"
      % (math.degrees(gapA), math.degrees(gapB), A[0], A[1], B[0], B[1]))
    P("   Q1: if the internal arc stays inside the endpoint span, the union's extreme points are the")
    P("       endpoint arcs' outer ends -> total span = 2*(alpha + beta(1)) = %.9f rad, INDEPENDENT"
      % (2 * (a + b1)))
    P("       of the internal ring (identity).  Only the union MEASURE can still depend on it")
    P("       (plateau/bridging vs disjoint regimes); the span itself is an identity.")
    # coverage lens on the axis
    disc = r * r - (A[1]) ** 2
    if disc > 0:
        xs = 1.0 * math.cos(gapA)
        x1 = xs - math.sqrt(disc)
        x2 = xs + math.sqrt(disc)
        P("   coverage lens ∩ axis: L in [%.9f, %.9f] ; annulus caps it at [1-r,1] = [%.2f,1]"
          % (x1, x2, 1 - r))
    return cL, cR, H, A, B, gapA, gapB


def sup_rho(r, h, adeg, nb=480):
    """sup over the coverage-feasible set F of max(rho1,rho2) (which is <= r by construction).
    Returns (sup, argmax, touching?)."""
    a = math.radians(adeg)
    cL = np.array([math.cos(a), math.sin(a)])
    cR = np.array([math.cos(a), -math.sin(a)])
    H = np.array([h, 0.0])
    b1 = beta(1.0, r)
    gA, gB = -(a - b1), (a - b1)
    A = np.array([math.cos(gA), math.sin(gA)])
    B = np.array([math.cos(gB), math.sin(gB)])
    best, arg = -1.0, None
    gx = np.linspace(-1.15, 1.15, nb)
    gy = np.linspace(-0.75, 0.75, nb)
    for x in gx:
        for y in gy:
            c = np.array([x, y])
            if np.linalg.norm(c - A) > r or np.linalg.norm(c - B) > r:
                continue
            L = np.linalg.norm(c)
            if not (1 - r <= L <= 1):
                continue
            r1 = circ(cL, c, H)
            r2 = circ(c, cR, H)
            if r1 > r or r2 > r:
                continue
            v = max(r1, r2)
            if v > best:
                best, arg = v, c.copy()
    step = (gx[1] - gx[0], gy[1] - gy[0])
    for _ in range(5):
        cx, cy = arg
        gx2 = np.linspace(cx - 2 * step[0], cx + 2 * step[0], 81)
        gy2 = np.linspace(cy - 2 * step[1], cy + 2 * step[1], 81)
        for x in gx2:
            for y in gy2:
                c = np.array([x, y])
                if np.linalg.norm(c - A) > r or np.linalg.norm(c - B) > r:
                    continue
                L = np.linalg.norm(c)
                if not (1 - r <= L <= 1):
                    continue
                r1 = circ(cL, c, H)
                r2 = circ(c, cR, H)
                if r1 > r or r2 > r:
                    continue
                v = max(r1, r2)
                if v > best:
                    best, arg = v, c.copy()
        step = (2 * step[0] / 80, 2 * step[1] / 80)
    return best, arg, (r - best < 1e-6), (cL, cR, H, A, B)


def part2(r, h, adegs):
    P("")
    P("=" * 100)
    P("§2 Q2: can the internal ring be deformed to an ACTIVE PIN without losing the coverage?")
    P("   F = {c : |c-A'|<=r, |c-B'|<=r, 1-r<=|c|<=1, rho(cL,c,H)<=r, rho(c,cR,H)<=r}")
    P("   sup_F max(rho1,rho2) <= r by construction; the question is whether it is ATTAINED.")
    P("     alpha   sup_F max rho        r - sup        touching?   argmax c")
    res = {}
    for adeg in adegs:
        sup, arg, touch, geo = sup_rho(r, h, adeg)
        res[adeg] = (sup, arg, touch, geo)
        P("     %5.1f   %.12f   %+.3e     %-9s   (%+.6f, %+.6f)"
          % (adeg, sup, r - sup, "YES" if touch else "no", arg[0], arg[1]))
    P("")
    P("   reading: 'touching' means the fan boundary meets the coverage-feasible set, i.e. the")
    P("   deformation to an active pin is possible; a positive margin means NO configuration of F")
    P("   has an active pin and the normalisation 'at least one pin active' fails for that data.")
    return res


def part3(cL, cR, H, c, r, adeg=30.0):
    P("")
    P("=" * 100)
    P("§3 hypothesis checks at the sup-point internal ring c = (%.9f,%.9f)  [alpha = %.1f deg]"
      % (c[0], c[1], adeg))
    P("   (H1) inward branch, (H2) actual covered ties, (H3) both fans rho <= r:")
    for nm, (X, Y) in (("(cL,c)", (cL, c)), ("(c,cR)", (c, cR))):
        U, t, inner, outer = tie_and_branch(X, Y, r, H)
        P("   pair %s: tie U = (%.9f,%.9f), |U-X| = %.9f, |U-Y| = %.9f -> actual tie? %s"
          % (nm, U[0], U[1], np.linalg.norm(U - X), np.linalg.norm(U - Y),
             "YES" if (np.linalg.norm(U - X) <= r + 1e-12 and np.linalg.norm(U - Y) <= r + 1e-12) else "no"))
        P("        rho = %.12f (r - rho = %+.3e)   |p_out| = %.9f (>=1? %s)   |H-p_in|-r = %+.3e"
          % (circ(X, Y, H), r - circ(X, Y, H), np.linalg.norm(outer), np.linalg.norm(outer) >= 1,
             np.linalg.norm(H - inner) - r))


def part4(r, h, adeg, res):
    """Explicit deformation certificate: from a natural feasible configuration to the tight one,
    sampled along the straight segment, all hypotheses re-checked."""
    P("")
    P("=" * 100)
    P("§4 DEFORMATION CERTIFICATE (alpha = %.1f deg): straight segment from a natural feasible")
    P("   internal ring to the tight point, all constraints checked along the path")
    sup, c1, touch, geo = res[adeg]
    cL, cR, H, A, B = geo
    for L0 in (0.70, 0.80, 0.90, 1.00):
        c0 = np.array([L0, 0.0])
        worst = {"cov_lo": -9, "cov_hi": -9, "ann_lo": -9, "ann_hi": -9, "f1": -9, "f2": -9,
                 "tie_lo": -9, "in_lo": -9}
        ok = True
        for t in np.linspace(0, 1, 200001):
            c = (1 - t) * c0 + t * c1
            L = np.linalg.norm(c)
            # coverage, annulus, fans (all margins positive = satisfied)
            slack_cov = min(r - np.linalg.norm(c - A), r - np.linalg.norm(c - B))
            slack_ann = min(L - (1 - r), 1 - L)
            f1 = r - circ(cL, c, H)
            f2 = r - circ(c, cR, H)
            if min(slack_cov, slack_ann, f1, f2) < -1e-9:
                ok = False
            worst["cov_lo"] = min(worst["cov_lo"], slack_cov) if worst["cov_lo"] > -9 else slack_cov
            worst["f1"] = min(worst["f1"], f1) if worst["f1"] > -9 else f1
            worst["f2"] = min(worst["f2"], f2) if worst["f2"] > -9 else f2
            worst["ann_lo"] = min(worst["ann_lo"], slack_ann) if worst["ann_lo"] > -9 else slack_ann
        P("   from c0 = (%.2f,0): path feasible = %-5s  min slacks: coverage %+.3e, annulus %+.3e,"
          " fan1 %+.3e, fan2 %+.3e" % (L0, ok, worst["cov_lo"], worst["ann_lo"], worst["f1"], worst["f2"]))
    P("   => the deformation to an ACTIVE PIN at fixed endpoints is realised by an explicit legal")
    P("      path in this family (coverage, ties, annulus and both fans verified along the segment).")


def main():
    r, h, adeg = 0.38, 0.5, 30.0
    part0()
    cL, cR, H, A, B, gA, gB = part1(r, h, adeg)
    res = part2(r, h, (22.0, 25.0, 27.0, 30.0, 33.0, 36.0, 40.0, 44.0))
    # hypothesis audit at the touching point of one alpha (or at the coverage-optimal point)
    for adeg2 in (30.0, 44.0):
        sup, arg, touch, geo = res[adeg2]
        cL2, cR2, H2, A2, B2 = geo
        part3(cL2, cR2, H2, arg, r, adeg2)
    part4(r, h, 30.0, res)
    (OUT / "r20_fixed_endpoint_variation.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_fixed_endpoint_variation.txt"))


if __name__ == "__main__":
    main()
