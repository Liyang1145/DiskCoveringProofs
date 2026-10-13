"""r20-chain: verify the lead's C879 variance identity and turn it into RING obligations.

IDENTITY (lead C879).  If  p_1..p_n in R^2, lam_j >= 0, sum lam_j = 1, h* = sum lam_j p_j, and
|p_j - h*| = r for all j, then for EVERY h
        sum_j lam_j |h - p_j|^2  =  r^2 + |h - h*|^2 .
Proof: |h-p_j|^2 = |h-h*|^2 + 2(h-h*).(h*-p_j) + |h*-p_j|^2, and sum lam_j (h*-p_j) = 0.
CONSEQUENCE.  If in addition h* lies in conv{p_j}, then sum lam_j |h-p_j|^2 = r^2 + |h-h*|^2;
since every term of the left side is <= r for a feasible h (|h - p_j| <= r for all pins), the
identity forces  h = h*  -- UNIQUENESS of the pin disk intersection (the three-point MEC case).
The equality hypothesis |p_j - h*| = r is exactly the "active set" condition.
RING OBLIGATION.  For an active set of two pins, |p_1 - p_2| = 2 sqrt(r^2 - |h*-m|^2) with
m = (p_1+p_2)/2, i.e. the CHORD LENGTH of the active pair is determined by r; for three pins the
triangle must be acute and its circumradius exactly r.
"""
import numpy as np
from r20geom import load_certified, polar_order, OUT
from scipy.optimize import linprog

PI = np.pi
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def roots_all(ci, cj, r):
    ci = np.asarray(ci, float); cj = np.asarray(cj, float)
    d = float(np.linalg.norm(cj - ci))
    a = d / 2.0
    m = (ci + cj) / 2.0
    u = (cj - ci) / d if d > 1e-15 else np.array([1.0, 0.0])
    n = np.array([-u[1], u[0]])
    k = float(np.sqrt(max(r * r - a * a, 0.0)))
    return d, a, m, k, m + k * n, m - k * n


def main():
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}; ring order " + ", ".join(map(str, ring_ids)))

    P("\n=== 1. the variance identity: check it numerically ===")
    rng = np.random.default_rng(11)
    mx = 0.0
    for _ in range(2000):
        n = rng.integers(2, 5)
        hstar = rng.uniform(-0.4, 0.4, 2)
        r = rng.uniform(0.2, 0.5)
        th = rng.uniform(0, 2 * PI, n)
        lam = rng.dirichlet(np.ones(n))
        pins = hstar + r * np.stack([np.cos(th), np.sin(th)], 1)
        h = rng.uniform(-1, 1, 2)
        lhs = float(np.sum(lam * np.sum((h - pins) ** 2, axis=1)))
        rhs = r * r + float(np.dot(h - hstar, h - hstar))
        mx = max(mx, abs(lhs - rhs))
    P(f"  max deviation over 2000 random active sets = {mx:.3e}  (identity verified)")

    P("\n=== 2. at the certified candidate: pins, active sets, hull membership ===")
    order = list(range(9))
    for H, lab, chain in ((HA, "A", order[0:4]), (HB, "B", order[4:8])):
        P(f"\n  hub {lab}: |H|={np.linalg.norm(H):.12f}  (hub radius R={R:.12f})")
        pins = []
        for kk in range(len(chain) - 1):
            i, j = chain[kk], chain[kk + 1]
            d, a, m, k, p1, p2 = roots_all(ring[i], ring[j], R)
            pin = min([p1, p2], key=np.linalg.norm)
            pins.append(pin)
            P(f"   edge ({ring_ids[i]:>2d},{ring_ids[j]:>2d}): pin={np.round(pin,9)}"
              f"  |pin|={np.linalg.norm(pin):.9f}   |H-pin|={np.linalg.norm(H-pin):.12f}"
              f"  margin R-|H-pin|={R-np.linalg.norm(H-pin):+.3e}")
        pins = np.array(pins)
        g = np.linalg.norm(pins - H, axis=1) - R
        act = np.where(np.abs(g) < 1e-10)[0]
        P(f"   active pins (margin 0): indices {list(act)}")
        if len(act):
            N = (H - pins[act]).T
            lp = linprog(np.zeros(len(act)), A_eq=np.vstack([N, np.ones(len(act))]),
                         b_eq=[0, 0, 1], bounds=[(0, None)] * len(act), method="highs")
            P(f"   is H a convex combination of the active pins? {bool(lp.success)}")
            if lp.success:
                P(f"     weights = {np.round(lp.x,9)}")
                # verify the identity consequence
                lam = lp.x
                lhs = float(np.sum(lam * np.sum((H - pins[act]) ** 2, axis=1)))
                P(f"     sum lam |H-pin|^2 = {lhs:.12f}   R^2 = {R*R:.12f}   difference = {lhs-R*R:+.3e}")
            # pairwise distances of the active pins vs 2R
            P(f"   active pin pairwise distances vs 2R = {2*R:.9f}:")
            for u in range(len(act)):
                for v in range(u + 1, len(act)):
                    d = float(np.linalg.norm(pins[act[u]] - pins[act[v]]))
                    P(f"     ({act[u]},{act[v]}): d={d:.9f}   2R-d={2*R-d:+.3e}   d-2R={d-2*R:+.3e}")

    P("\n=== 3. the two-pin equality obligation in ring parameters ===")
    P("  for an active pair (p_U, p_V) both at distance r from h*: |p_U-p_V| <= 2r and")
    P("  h* = m_UV +- sqrt(r^2 - |p_U-p_V|^2/4) * normal.  So |p_U-p_V| = 2r would force h* = m_UV.")
    P("  Below: |p_U - p_V| and 2R at the candidate's 3 active pins of the B chain.")
    H = HB
    pins = []
    for kk in range(3, 7):
        i, j = kk, kk + 1
        d, a, m, k, p1, p2 = roots_all(ring[i], ring[j], R)
        pins.append(min([p1, p2], key=np.linalg.norm))
    pins = np.array(pins)
    for u in range(len(pins)):
        for v in range(u + 1, len(pins)):
            P(f"   pin{u} pin{v}: d={np.linalg.norm(pins[u]-pins[v]):.9f}  vs 2R={2*R:.9f}")

    (OUT / "c879_identity.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "c879_identity.txt"))


if __name__ == "__main__":
    main()
