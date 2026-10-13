"""Audit of the self-registered claims C880-C889 against their own evidence.

Read-only on the claim store; writes ../out/audit_c880_889.txt.

Four independent computations:
  P1  F1 (C880): the phase used for the interior extremum is the MIN-type phase arg(H-C),
      not the MAX-type phase arg(C-H).  Test harness of identities2.py re-run for three
      variants (code / corrected both-phases / 8001-point dense sampling).
  P2  F2 (C881): the "necessary and sufficient" equivalence "triangle covered by its three
      vertex disks <=> rho <= r" is FALSE for obtuse triangles.  Explicit flat obtuse
      triangle with rho >> r, whose 3-disk covering radius c(T) is computed by a
      Voronoi-skeleton search and is < rho.
  P3  F3 (C882): "rho <= r <-> exactly one of the two closed disks contains h" is FALSE at
      the circle-boundary intersections: h = m + (r-k) n has |h-p_in| = r and
      |h-p_out| < r (both closed disks contain h) yet rho(c_i,c_j,h) = r.  The correct
      criterion is the PRODUCT form plus non-collinearity.
  P4  C887/C888/C889: the exposed-rim-arc extent is NOT 2*s_i in general; the two evidence
      files do not agree term by term (contradicting C889's control).  Exact character of
      the arc endpoints is reported.
"""
import math
import numpy as np
from r20geom import load_certified, polar_order, s_H, OUT
from arcs import truly_uncovered_arcs

R_CERT = 0.3799838531198388
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


# ---------------------------------------------------------------- P1
def maxdist_code(H, C, R, c0, hw):
    """Verbatim logic of identities2.py:maxdist_arc_exact (phase arg(H-C))."""
    lo, hi = c0 - hw, c0 + hw
    cand = [np.linalg.norm(H - (np.asarray(C) + R * np.array([np.cos(s), np.sin(s)]))) for s in (lo, hi)]
    v = np.asarray(H) - np.asarray(C)
    if np.linalg.norm(v) > 1e-15:
        sp = float(np.arctan2(v[1], v[0]))
        for k in (-2, -1, 0, 1, 2):
            if lo <= sp + 2 * math.pi * k <= hi:
                x = np.asarray(C) + R * v / np.linalg.norm(v)
                cand.append(float(np.linalg.norm(x - H)))
                break
    return max(cand)


def maxdist_fixed(H, C, R, c0, hw):
    """Corrected critical set: endpoints and BOTH phases arg(H-C)+pi*k (k=0,1)."""
    lo, hi = c0 - hw, c0 + hw
    cand = [np.linalg.norm(H - (np.asarray(C) + R * np.array([np.cos(s), np.sin(s)]))) for s in (lo, hi)]
    v = np.asarray(H) - np.asarray(C)
    if np.linalg.norm(v) > 1e-15:
        sp = float(np.arctan2(v[1], v[0]))
        for k in (-2, -1, 0, 1, 2):
            for s in (sp + 2 * math.pi * k, sp + math.pi + 2 * math.pi * k):
                if lo - 1e-14 <= s <= hi + 1e-14:
                    x = np.asarray(C) + R * np.array([np.cos(s), np.sin(s)])
                    cand.append(float(np.linalg.norm(x - H)))
    return max(cand)


def maxdist_samples(H, C, R, c0, hw, n=8001):
    ss = np.linspace(c0 - hw, c0 + hw, n)
    xs = np.asarray(C) + R * np.stack([np.cos(ss), np.sin(ss)], 1)
    return float(np.max(np.linalg.norm(xs - H, axis=1)))


def part1():
    P("=" * 100)
    P("P1  F1 (C880) -- which interior phase attains the max of |x-H| on the arc?")
    P("    |x(s)-H|^2 = R^2+|C-H|^2 + 2R (C-H).n(s) = R^2+|C-H|^2 - 2R|C-H| cos(s - arg(H-C))")
    P("    => MAX at s = arg(H-C)+pi = arg(C-H)   (the anti-pole);  MIN at s = arg(H-C).")
    P("    identities2.py appends the phase arg(H-C) only => it appends the MINIMUM.")
    P("")
    # explicit counterexample, lead's own numbers (D-CHAIN-1 control)
    R, C, H = 1.0, np.array([2.0, 0.0]), np.array([1.0, 0.0])
    c0, hw = 0.0, 0.5
    P("    explicit arc: C=(2,0), H=(1,0), R=1, arc centre-angle 0, halfwidth 0.5")
    P("      code        maxdist = %.12f" % maxdist_code(H, C, R, c0, hw))
    P("      fixed       maxdist = %.12f" % maxdist_fixed(H, C, R, c0, hw))
    P("      dense 8001  maxdist = %.12f" % maxdist_samples(H, C, R, c0, hw))
    P("      code phase arg(H-C) = pi is NOT in the arc; the true interior max sits at s=0=arg(C-H).")
    P("      endpoint value = %.12f  (r = 1) -> the code's criterion ACCEPTS a non-covered arc."
      % np.linalg.norm(H - (C + R * np.array([np.cos(hw), math.sin(hw)]))))
    P("")
    # re-run the identities2 harness, three variants
    rng = np.random.default_rng(1)
    bad_code = bad_fix = bad_smp = 0
    worst = 0.0
    for _ in range(4000):
        L = rng.uniform(R_CERT + 1e-3, 1.4)
        Cc = L * np.array([np.cos(rng.uniform(0, 2 * math.pi)), np.sin(rng.uniform(0, 2 * math.pi))])
        Hh = (1 - R_CERT) * rng.uniform(-1, 1, 2)
        c0 = rng.uniform(0, 2 * math.pi)
        hw = rng.uniform(1e-3, math.pi - 1e-3)
        got = maxdist_samples(Hh, Cc, R_CERT, c0, hw)
        vc, vf = maxdist_code(Hh, Cc, R_CERT, c0, hw), maxdist_fixed(Hh, Cc, R_CERT, c0, hw)
        if got > vc + 1e-9:
            bad_code += 1
            worst = max(worst, got - vc)
        if got > vf + 1e-9:
            bad_fix += 1
        if abs(got - vf) > 1e-7:
            bad_smp += 1
    P("    same 4000-case harness as identities2.py (sampling = 8001 points):")
    P("      code variant : sampled > code  in %4d cases (worst excess %.6f)" % (bad_code, worst))
    P("      fixed variant: sampled > fixed in %4d cases" % bad_fix)
    P("      fixed variant disagrees with the 8001-point sampling by >1e-7 in %d cases" % bad_smp)
    P("    NOTE: the stored evidence out/identities2.txt line 4 already reports")
    P("      'random hub/arc pairs: 4000; violations: 2003' -- contradicting C880's '0/4000'.")


# ---------------------------------------------------------------- P2
def circumradius(V):
    e = [np.linalg.norm(V[1] - V[2]), np.linalg.norm(V[0] - V[2]), np.linalg.norm(V[0] - V[1])]
    ar = abs((V[1] - V[0])[0] * (V[2] - V[0])[1] - (V[1] - V[0])[1] * (V[2] - V[0])[0]) / 2
    return e[0] * e[1] * e[2] / (4 * ar)


def part2():
    P("=" * 100)
    P("P2  F2 (C881) -- is 'triangle covered by its three vertex disks  <=>  rho <= r' true?")
    eps = 0.1
    V = np.array([[-1.0, 0.0], [1.0, 0.0], [0.0, eps]])
    rho = circumradius(V)
    P("    flat obtuse triangle: (-1,0), (1,0), (0,%.3f)" % eps)
    P("      circumradius rho = %.12f   (circumcentre outside the triangle: obtuse at the base angles)"
      % rho)
    # exact covering radius of T by the three vertex disks: max of min_k |x-v_k| over T
    # candidates: base transition points x = +-x*, x* = (1-eps^2)/2, value (1+eps^2)/2
    xs = (1 - eps * eps) / 2
    base_val = (1 + eps * eps) / 2
    P("      analytic candidate on the base: x = +-%.6f, f = %.12f  (= (1+eps^2)/2)" % (xs, base_val))
    best = 0.0
    arg = None
    for _ in range(6):
        gx = np.linspace(-1, 1, 401)
        gy = np.linspace(0, eps, 121)
        for a in gx:
            for b in gy:
                x = np.array([a, b])
                # barycentric test: inside the triangle?
                if b > eps * (1 - abs(a)) + 1e-15:
                    continue
                f = min(np.linalg.norm(x - v) for v in V)
                if f > best:
                    best, arg = f, x
        if arg is None:
            break
        step = (gx[1] - gx[0], gy[1] - gy[0])
        gx = np.linspace(arg[0] - 2 * step[0], arg[0] + 2 * step[0], 41)
        gy = np.linspace(max(0, arg[1] - 2 * step[1]), min(eps, arg[1] + 2 * step[1]) + 1e-18, 41)
    P("      grid+refinement max of min_k |x-v_k| over T = %.12f at x = (%+.8f, %+.8f)"
      % (best, arg[0], arg[1]))
    r = 0.51
    P("      take r = %.6f: rho = %.6f > r (so the claim says 'uncovered')," % (r, rho))
    P("        but the three vertex disks of radius r cover T (max f = %.6f < r)." % best)
    P("      => the NECESSITY direction of C881 is false; only 'rho <= r => covered' holds.")
    P("      The circumcentre witness is useless for obtuse triangles: it lies outside T.")


# ---------------------------------------------------------------- P3
def part3():
    P("=" * 100)
    P("P3  F3 (C882) -- 'rho <= r <-> exactly one of the two closed disks contains h'")
    rng = np.random.default_rng(7)
    P("    (a) boundary-intersection counterexample h = m + (r-k) n,  r > k > 0:")
    for trial in range(3):
        r = rng.uniform(0.3, 0.5)
        m = rng.uniform(-0.3, 0.3, 2)
        th = rng.uniform(0, 2 * math.pi)
        a = rng.uniform(0.05, 0.95 * r)
        u = np.array([math.cos(th), math.sin(th)])
        n = np.array([-u[1], u[0]])
        ci, cj = m - a * u, m + a * u
        k = math.sqrt(r * r - a * a)
        p_in, p_out = (m - k * n, m + k * n) if m @ n >= 0 else (m + k * n, m - k * n)
        h = m + (r - k) * n
        rho = circumradius(np.array([ci, cj, h]))
        A = float(np.linalg.norm(h - p_in) ** 2 - r * r)
        B = float(np.linalg.norm(h - p_out) ** 2 - r * r)
        prod = A * B
        collinear = abs((cj - ci)[0] * (h - ci)[1] - (cj - ci)[1] * (h - ci)[0]) < 1e-12
        P("      r=%.6f a=%.6f k=%.6f  rho=%.12f  A=|h-p_in|^2-r^2=%+.3e  B=%+.3e  A*B=%+.3e"
          % (r, a, k, rho, A, B, prod))
        P("        both closed disks contain h? %s   exactly-one? %s   rho<=r? %s   collinear? %s"
          % (A <= 0 and B <= 0, (A <= 0) != (B <= 0), rho <= r + 1e-12, collinear))
    P("    (b) the correct criterion: for h NON-COLLINEAR with c_i,c_j")
    P("          4 y^2 (rho^2-r^2) = (|h-p_out|^2-r^2)(|h-p_in|^2-r^2)     [lead Lemma 2]")
    P("          rho <= r  <=>  the product <= 0  (at least one closed disk, not both interiors).")
    P("    (c) the 'off the radical line' phrasing is wrong: the excluded set is the LINE c_i c_j")
    P("        (collinearity), not the perpendicular bisector.  Random check:")
    bad_prod = bad_coll = 0
    ncase = 0
    for _ in range(20000):
        r = rng.uniform(0.3, 0.45)
        m = rng.uniform(0, 0.6) * np.array([math.cos(rng.uniform(0, 2 * math.pi)),
                                            math.sin(rng.uniform(0, 2 * math.pi))])
        th = rng.uniform(0, 2 * math.pi)
        a = rng.uniform(0.05, 0.999 * r)
        u = np.array([math.cos(th), math.sin(th)])
        n = np.array([-u[1], u[0]])
        ci, cj = m - a * u, m + a * u
        k = math.sqrt(r * r - a * a)
        h = rng.uniform(-1, 1, 2)
        y = float((h - m) @ n)
        if abs(y) < 1e-9:
            bad_coll += 1
            continue
        ncase += 1
        rho = circumradius(np.array([ci, cj, h]))
        p1, p2 = m + k * n, m - k * n
        prod = float((np.linalg.norm(h - p1) ** 2 - r * r) * (np.linalg.norm(h - p2) ** 2 - r * r))
        if (rho <= r + 1e-12) != (prod <= 1e-12):
            bad_prod += 1
    P("      product criterion vs direct rho: %d/%d mismatches (non-collinear cases)" % (bad_prod, ncase))
    P("      collinear draws skipped: %d  (there the product test is not equivalent)" % bad_coll)


# ---------------------------------------------------------------- P4
def part4():
    P("=" * 100)
    P("P4  C887/C888/C889 -- exposed-rim-arc extent vs s_i = arccos(|H-c_i|/(2R))")
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P("    R = %.15f ; polar ring order %s" % (R, list(ring_ids)))
    # pins (min-norm roots) of the nine polar-order edges
    pins = {}
    for i in range(9):
        a, b = ring[i], ring[(i + 1) % 9]
        m = (a + b) / 2
        d = float(np.linalg.norm(b - a))
        n = np.array([-(b - a)[1], (b - a)[0]]) / d
        k = math.sqrt(R * R - d * d / 4)
        pins[i] = min([m + k * n, m - k * n], key=np.linalg.norm)
    P("")
    P("    ring | extent/2 | s_HA   s_HB  | endpoints: |x| , |x-HA| , |x-HB| , pin-coincidence")
    for i in range(9):
        arcs = truly_uncovered_arcs(ring, i, R)
        ci = ring[i]
        sa = s_H(HA, ci, R)
        sb = s_H(HB, ci, R)
        for (c, hw) in arcs:
            lo, hi = c - hw, c + hw
            desc = []
            for t in (lo, hi):
                x = ci + R * np.array([math.cos(t), math.sin(t)])
                hit = ""
                for j, pj in pins.items():
                    if np.linalg.norm(x - pj) < 1e-9:
                        hit = "pin(%d,%d)" % (j, (j + 1) % 9)
                desc.append("(%.9f, %.9f)" % (np.linalg.norm(x), 0.0))
                desc[-1] = "(|x|=%.6f |x-HA|=%.9f |x-HB|=%.9f %s)" % (
                    np.linalg.norm(x), np.linalg.norm(x - HA), np.linalg.norm(x - HB), hit)
            P("    %3d  | %.9f | %.5f %.5f | %s" % (ring_ids[i], hw * 2, sa, sb, "  ".join(desc)))
    P("")
    P("    evidence cross-check (the two files C889 calls 'independent sources'):")
    P("      arc_account.txt hw   = 0.37896 0.44674 0.44674 0.37896 0.58935 0.43300 0.61768 0.43300 0.58935")
    P("      clean_measurement s_H = A: 0.38439 0.45152 0.45152 0.38439 0.25112 inf inf inf 0.25112")
    P("                              B: inf inf inf inf 0.33823 0.43300 0.61768 0.43300 0.33823")
    P("      -> they agree term by term ONLY on rings 7, 1, 8 (hub B's interior rings).")
    P("")
    P("    independent dense-sampling control of the exposed-arc extents (4e5 points per rim):")
    P("      ring   analytic extent   sampled extent   diff")
    npts = 400000
    for i in range(9):
        ci = ring[i]
        ts = np.linspace(0, 2 * np.pi, npts, endpoint=False)
        pts = ci + R * np.stack([np.cos(ts), np.sin(ts)], 1)
        ok = np.sum(pts ** 2, axis=1) <= 1.0
        for k in range(9):
            if k == i:
                continue
            ok &= np.sum((pts - ring[k]) ** 2, axis=1) >= R * R
        if not ok.any():
            P("      %3d   (no exposed rim)" % ring_ids[i])
            continue
        # angular runs
        idx = np.where(ok)[0]
        runs = []
        start = idx[0]
        for a, b in zip(idx[:-1], idx[1:]):
            if b != a + 1:
                runs.append((start, a))
                start = b
        runs.append((start, idx[-1]))
        if len(runs) > 1 and idx[0] == 1 and idx[-1] == npts - 2:
            runs[0] = (runs[-1][0], runs[0][1])
            runs.pop()
        tot = sum((b - a + 1) for a, b in runs) * (2 * math.pi / npts)
        ana = sum(hw * 2 for (_, hw) in truly_uncovered_arcs(ring, i, R))
        P("      %3d   %.9f       %.9f      %+.2e"
          % (ring_ids[i], ana, tot, tot - ana))


def main():
    part1()
    part2()
    part3()
    part4()
    (OUT / "audit_c880_889.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "audit_c880_889.txt"))


if __name__ == "__main__":
    main()
