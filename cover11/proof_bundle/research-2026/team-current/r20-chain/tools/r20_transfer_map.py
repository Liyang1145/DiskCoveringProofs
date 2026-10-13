"""r20 chain transfer map / rotation number (lead's analytic thread, 2026-09-25).

Read-only outside r20-chain; writes ../out/r20_transfer_map.txt.

P1  PER-EDGE TRANSFER MAP (exact).  Hub H, radius r, rings c_i,c_{i+1} with spokes
    d=|H-c| <= 2r and s = arccos(d/(2r)) in [0,pi/2]; theta = angle c_i H c_{i+1} in (0,pi).
    Then   rho(c_i,c_{i+1},H) <= r   <=>   |s_i - s_{i+1}| <= theta <= s_i + s_{i+1},
    and equality on either side <=> rho = r <=> H on the boundary of one of the two radius-r
    circle centres through (c_i,c_{i+1})  (the pin-tight configuration).
    Proof: rho = |c_i c_{i+1}|/(2 sin theta) (law of sines); the inequality is a quadratic in
    cos theta whose endpoints are cos(s_i+s_{i+1}) and cos(s_i-s_{i+1}) (see the report).
P2  CHAIN / ROTATION NUMBER: for a legal chain, sum theta_i in [sum|s_i-s_{i+1}|, sum(s_i+s_{i+1})];
    the all-tight configuration (theta_i = s_i+s_{i+1} for every edge) is realizable for any spoke
    sequence, so the span maximum for given spokes is ATTAINED AT PIN EQUALITY.
    For a full cycle around the hub (sum theta = 2pi, all spokes <= 2r): sum_i s_i >= pi.
P3  record configuration cross-check: tight edges = active pins.
P4  COUNTEREXAMPLE for other functionals: the covered unit-boundary measure can be maximised at a
    strictly non-tight configuration (explicit family), so tightness is a property of the TURN
    functional, not a WLOG for every extremal problem.
"""
import json, math
import numpy as np
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "out"
ROOT = HERE.parents[3]
OBJ = ROOT / "n11" / "upper" / "certified_object.json"
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def circ(A, B, C):
    e = [np.linalg.norm(B - C), np.linalg.norm(A - C), np.linalg.norm(A - B)]
    ar = abs((B[0] - A[0]) * (C[1] - A[1]) - (B[1] - A[1]) * (C[0] - A[0])) / 2
    return e[0] * e[1] * e[2] / (4 * ar) if ar > 1e-15 else np.inf


def part1():
    P("=" * 100)
    P("P1  PER-EDGE TRANSFER MAP  rho <= r  <=>  |s_i - s_{i+1}| <= theta <= s_i + s_{i+1}")
    rng = np.random.default_rng(3)
    bad = bad_tol = bad_eq = 0
    n = 0
    eqcases = 0
    for _ in range(20000):
        r = rng.uniform(0.3, 0.45)
        H = rng.uniform(-0.5, 0.5, 2)
        a = rng.uniform(1 - r, 1.0)
        b = rng.uniform(1 - r, 1.0)
        ta = rng.uniform(0, 2 * math.pi)
        tb = ta + rng.uniform(0.02, math.pi - 0.02)
        ca = a * np.array([math.cos(ta), math.sin(ta)])
        cb = b * np.array([math.cos(tb), math.sin(tb)])
        da, db = np.linalg.norm(ca - H), np.linalg.norm(cb - H)
        if da > 2 * r or db > 2 * r:
            continue
        sa = math.acos(da / (2 * r))
        sb = math.acos(db / (2 * r))
        va, vb = ca - H, cb - H
        th = math.acos(np.clip(va @ vb / np.linalg.norm(va) / np.linalg.norm(vb), -1, 1))
        rho = circ(ca, cb, H)
        n += 1
        pred = (abs(sa - sb) <= th + 1e-12) and (th <= sa + sb + 1e-12)
        got = rho <= r + 1e-12
        if pred != got:
            bad += 1
        # equality characterisation (only meaningful when the pair is radially compatible)
        m = (ca + cb) / 2
        d = np.linalg.norm(cb - ca)
        if d > 2 * r:
            continue
        nn = np.array([-(cb - ca)[1], (cb - ca)[0]]) / d
        k = math.sqrt(r * r - d * d / 4)
        p1_, p2_ = m + k * nn, m - k * nn
        tight_pin = min(abs(np.linalg.norm(H - p1_) - r), abs(np.linalg.norm(H - p2_) - r)) < 1e-9
        tight_turn = min(abs(th - (sa + sb)), abs(th - abs(sa - sb))) < 1e-9
        if tight_pin or tight_turn:
            eqcases += 1
            if tight_pin != tight_turn:
                bad_eq += 1
    P("    cases with both spokes <= 2r: %d ; mismatches of the map: %d" % (n, bad))
    P("    (|s_i-s_{i+1}| <= theta <= s_i+s_{i+1}): mismatches with rho<=r: %d" % bad)
    P("    equality at an interval end vs pin-tightness mismatch: %d / %d equality cases"
      % (bad_eq, eqcases))
    # all-tight realizability (P2)
    P("")
    P("P2  all-tight configuration is realizable for any spoke sequence; span = sum(s_i+s_{i+1})")
    bad2 = 0
    for _ in range(3000):
        H = rng.uniform(-0.5, 0.5, 2)
        r = rng.uniform(0.32, 0.42)
        m = int(rng.integers(2, 7))
        s = rng.uniform(0.05, 1.2, m)            # spokes 2r cos(s) <= 2r
        phi = np.cumsum(np.r_[rng.uniform(0, 1), s[:-1] + s[1:]])   # all-tight turns
        c = np.array([H + 2 * r * math.cos(s[k]) * np.array([math.cos(phi[k]), math.sin(phi[k])])
                      for k in range(m)])
        for k in range(m - 1):
            rho = circ(c[k], c[k + 1], H)
            if abs(rho - r) > 1e-9:
                bad2 += 1
    P("    random all-tight chains: |rho - r| > 1e-9 in %d / 3000" % bad2)
    bad3 = 0
    for _ in range(3000):
        H = rng.uniform(-0.5, 0.5, 2)
        r = rng.uniform(0.32, 0.42)
        sa, sb = rng.uniform(0.05, 1.2, 2)
        th = abs(sa - sb)                       # the OTHER extreme of the interval
        # place cb at angle th from ca about H
        da, db = 2 * r * math.cos(sa), 2 * r * math.cos(sb)
        ca = H + da * np.array([1.0, 0.0])
        cb = H + db * np.array([math.cos(th), math.sin(th)])
        if abs(circ(ca, cb, H) - r) > 1e-9:
            bad3 += 1
    P("    other extreme theta = |s_i-s_{i+1}|: |rho - r| > 1e-9 in %d / 3000" % bad3)
    P("    => BOTH interval endpoints are exactly the pin-tight (rho = r) configurations.")
    P("    => for FIXED spokes the maximum turn sum is exactly the all-tight one (sum of caps),")
    P("       attained at pin equality; no saturation/equal-angle premise is used.")
    P("    corollary (closed cycle, all spokes <= 2r): 2pi = sum theta_i <= 2 sum s_i  =>  sum s_i >= pi")


def part3(c, rings, HUB_A, HUB_B, R, allpins):
    P("")
    P("=" * 100)
    P("P3  record configuration: per-edge turn vs cap, and the tight <-> active-pin correlation")
    for nm, H, chain in (("hub A", HUB_A, [4, 5, 6, 7, 8]), ("hub B", HUB_B, [0, 1, 2, 3])):
        P("   %s (|H| = %.9f):" % (nm, np.linalg.norm(H)))
        tot = capsum = 0.0
        for i in chain:
            ca, cb = c[i], c[(i + 1) % 9]
            va, vb = ca - H, cb - H
            th = math.acos(np.clip(va @ vb / np.linalg.norm(va) / np.linalg.norm(vb), -1, 1))
            sa = math.acos(np.linalg.norm(va) / (2 * R))
            sb = math.acos(np.linalg.norm(vb) / (2 * R))
            pin = allpins[i][0]
            dpin = np.linalg.norm(pin - H)
            tot += th
            capsum += sa + sb
            P("     edge (%d,%d): theta=%.9f  cap=s_i+s_j=%.9f  cap-theta=%+.3e   |H-pin|-r=%+.3e %s"
              % (i, (i + 1) % 9, th, sa + sb, sa + sb - th, dpin - R,
                 "TIGHT" if sa + sb - th < 1e-9 else ""))
        P("     span sum theta = %.9f   cap sum = %.9f   slack = %+.6f" % (tot, capsum, capsum - tot))


def part4():
    P("")
    P("=" * 100)
    P("P4  COUNTEREXAMPLE for a coverage-type functional: the maximiser can be strictly NON-tight")
    r = 0.38
    H = np.array([0.5, 0.0])

    def beta(L):
        return math.acos((1 + L * L - r * r) / (2 * L))

    Lstar = math.sqrt(1 - r * r)
    P("   hub H=(0.5,0), r=%.2f.  A ring at |c|=L covers on dD an arc of half-width" % r)
    P("     beta(L) = arccos((1+L^2-r^2)/(2L)), which is maximised at L* = sqrt(1-r^2) = %.9f;" % Lstar)
    P("     beta(L*) = arcsin(r) = %.9f rad = %.6f deg,  beta(1) = %.9f"
      % (beta(Lstar), math.degrees(beta(Lstar)), beta(1.0)))
    P("   family: pair at azimuths +-alpha, common radius L in [1-r, 1]; functional")
    P("     Phi(L) = angular measure of dD covered by the two disks (monotone in beta(L)),")
    P("     legality: rho(c_1,c_2,H) <= r.")
    P("   alpha     Phi argmax L   beta at argmax   rho at argmax   r - rho")
    for alpha_deg in (5.0, 10.0, 15.0, 20.0, 22.0, 25.0):
        al = math.radians(alpha_deg)
        best, argL = -1.0, None
        for L in np.linspace(1 - r, 1.0, 20001):
            c1 = L * np.array([math.cos(al), math.sin(al)])
            c2 = L * np.array([math.cos(al), -math.sin(al)])
            if circ(c1, c2, H) > r + 1e-13:
                continue
            b = beta(L)
            # connected case span = 2(alpha+beta) when beta>=alpha, else 4*beta (disjoint)
            phi = 2 * (al + b) if b >= al else 4 * b
            if phi > best:
                best, argL = phi, L
        c1 = argL * np.array([math.cos(al), math.sin(al)])
        c2 = argL * np.array([math.cos(al), -math.sin(al)])
        rho = circ(c1, c2, H)
        P("   %5.1f      %.6f     %.9f      %.9f     %+.6e"
          % (alpha_deg, argL, beta(argL), rho, r - rho))
    P("")
    P("   reading: for small alpha the legality is strictly slack at the maximiser (the arc-width")
    P("   functional peaks at L* interior to the legal set); for larger alpha L* is illegal and the")
    P("   maximiser sits on the legality boundary (rho = r exactly).  Hence 'extremum => pin'")
    P("   equality' is TRUE for the turn functional (P1/P2) and FALSE for coverage functionals.")
    P("   The mechanism is visible: the legality constraint is NOT monotone in L")
    P("   (rho(0.62)=%.4f, rho(L*)=%.4f, rho(1)=%.4f), so its boundary need not carry the max."
      % (circ((1 - r) * np.array([math.cos(0.2), math.sin(0.2)]),
             (1 - r) * np.array([math.cos(0.2), -math.sin(0.2)]), H),
         circ(Lstar * np.array([math.cos(0.2), math.sin(0.2)]),
              Lstar * np.array([math.cos(0.2), -math.sin(0.2)]), H),
         circ(np.array([math.cos(0.2), math.sin(0.2)]),
              np.array([math.cos(0.2), -math.sin(0.2)]), H)))


def main():
    part1()
    raw = json.loads(OBJ.read_text(encoding="utf-8-sig"))
    C0 = np.array([[int(v) / 1e17 for v in a] for a in raw["centers_scaled_1e17"]])
    R = float(raw["certified_interval"]["lo"])
    rings = sorted([i for i in range(11) if i not in (0, 2)],
                   key=lambda i: math.atan2(C0[i, 1], C0[i, 0]))
    C = C0[rings + [0, 2]]
    c = C[[(i + 4) % 9 for i in range(9)] + [10, 9]]
    HUB_A, HUB_B = c[10], c[9]
    allpins = {}
    for i in range(9):
        a, b = c[i], c[(i + 1) % 9]
        m = (a + b) / 2
        d = float(np.linalg.norm(b - a))
        nn = np.array([-(b - a)[1], (b - a)[0]]) / d
        k = math.sqrt(R * R - d * d / 4)
        allpins[i] = (min([m + k * nn, m - k * nn], key=np.linalg.norm),)
    part3(c, rings, HUB_A, HUB_B, R, allpins)
    part4()
    (OUT / "r20_transfer_map.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_transfer_map.txt"))


if __name__ == "__main__":
    main()
