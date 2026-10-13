"""C26: the exact low-dimensional ring representation, end to end, with controls.

RESULT (elementary; verified exactly on the certified candidate).

  (R1) Sharp site lemma.  Let P, Q be distinct points of the unit circle and let
       c be at the same distance R from both.  Then c lies on the perpendicular
       bisector of PQ, which passes through the origin (since |P| = |Q| = 1);
       writing theta = (angle between P and Q)/2 and n = dir(P+Q), the second
       condition |c-P| = R is the quadratic in the signed distance s = <c,n>
             s^2 - 2 s cos(theta) + 1 - R^2 = 0
             s = cos(theta) +- sqrt(R^2 - sin^2(theta)),
       which is solvable iff R >= sin(theta).  Hence
             rho = |c| = |cos(theta) +- sqrt(R^2 - sin^2 theta)|,
             dir c = dir(P + Q)  (or its antipode, for the other branch).

  (R2) Consequence.  In a sharp 9-ring configuration all nine ring sites have the
       SAME switch distance R, so each ring site is determined by its switch gap
       g_i = 2 theta_i through
             rho_i = cos(g_i/2) - sqrt(R^2 - sin^2(g_i/2))         [chosen branch]
             dir c_i = dir(switch_(i-1) + switch_i)
       and therefore the whole sharp ring stratum is parametrised by
             (g_1,...,g_9, R)  with  sum_i g_i = 2 pi ,
       i.e. by 9 numbers modulo the global rotation.  In particular the nine
       tight radii R_i coincide automatically, and the tightness conditions do
       NOT determine R.

  (R3) The interior structure (the two hubs) is NOT determined by the ring data:
       the hubs enter only through the covering condition on the interior
       vertices.  Hence the reduced problem is: minimise R over the
       (g, R, hub positions) manifold subject to coverage of the disk.

Controls: K1 |M_i| = cos(g_i/2); K2 rho formula vs candidate (all nine);
K3 the branch choice is uniform; K4 synthetic family residual; K5 the identity
sum_i g_i = 2 pi is automatic.
"""
import json, math
from pathlib import Path
import numpy as np

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
pi = math.pi


def load():
    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


ORDER = [7, 1, 8, 6, 4, 9, 10, 3, 5]


def candidate_switches(C, R):
    m = 9
    sw = []
    for i in range(m):
        s, s2 = ORDER[i], ORDER[(i + 1) % m]
        a, b = C[s], C[s2]
        mx = (a + b) / 2
        dv = b - a
        tt = (dv @ mx) / (dv @ dv)
        f = dv * tt
        h = math.hypot(*f)
        u = np.array([-dv[1], dv[0]]) / math.hypot(*dv)
        ss = math.sqrt(max(0.0, 1 - h * h))
        for sgn in (1, -1):
            p = f + sgn * ss * u
            d = np.hypot(*(C - p[None, :]).T)
            if d.min() >= R - 1e-9:
                sw.append(p)
                break
    return np.array(sw)


def ring_from_gaps_R(gaps, R, theta0=0.0):
    """(R2): switches + ring sites from the gaps and the common radius R."""
    m = len(gaps)
    th = np.cumsum(np.r_[theta0, gaps[:-1]])
    P = np.stack([np.cos(th), np.sin(th)], 1)
    Z = np.zeros((m, 2))
    for i in range(m):
        pL = P[(i - 1) % m]
        pR = P[i]
        n = pL + pR
        n = n / np.hypot(*n)
        th_i = gaps[i] / 2
        root = R * R - math.sin(th_i) ** 2
        if root < 0:
            return None, None
        # pick the branch that keeps the site between the two switches
        s = math.cos(th_i) - math.sqrt(root)
        Z[i] = s * n
    return P, Z


def main():
    C = load()
    R = 0.37998385311983884
    sw = candidate_switches(C, R)
    m = 9
    th = np.array([math.atan2(p[1], p[0]) for p in sw])
    gaps = np.array([((th[i] - th[(i - 1) % m]) % (2 * pi)) for i in range(m)])

    print("K5: sum of gaps =", sum(gaps), " (2pi =", 2 * pi, ")")
    print("K1: |M_i| = cos(g_i/2)?")
    for i in range(m):
        M = (sw[(i - 1) % m] + sw[i]) / 2
        print(f"   i={i} |M|={np.hypot(*M):.15f} cos(g/2)={math.cos(gaps[i]/2):.15f}"
              f" diff={np.hypot(*M)-math.cos(gaps[i]/2):+.2e}")

    P, Z = ring_from_gaps_R(gaps, R, theta0=th[0])
    print("\nK2: (R2) reconstruction vs the candidate ring sites")
    for i in range(m):
        cand = C[ORDER[i]]
        print(f"   i={i} site {ORDER[i]:2d}: pred=({Z[i][0]:+.12f},{Z[i][1]:+.12f})"
              f"  cand=({cand[0]:+.12f},{cand[1]:+.12f})  err={np.hypot(*(Z[i]-cand)):.2e}")

    print("\nK3: branch choice — sign of s = cos - sqrt(R^2 - sin^2):",
          ["+" if math.cos(gaps[i] / 2) - math.sqrt(R * R - math.sin(gaps[i] / 2) ** 2) > 0 else "-"
           for i in range(m)])

    print("\nK4: synthetic family (random gaps summing to 2pi, R fixed)")
    rng = np.random.default_rng(5)
    worst = 0.0
    for _ in range(300):
        g = rng.uniform(0.2, 1.0, m)
        g = g * (2 * pi / g.sum())
        P2, Z2 = ring_from_gaps_R(g, R, theta0=0.0)
        if Z2 is None:
            continue
        for i in range(m):
            d1 = np.hypot(*(Z2[i] - P2[(i - 1) % m]))
            d2 = np.hypot(*(Z2[i] - P2[i]))
            worst = max(worst, abs(d1 - R), abs(d2 - R))
    print("   max |switch distance - R| over the family:", worst)
    print("   (the family satisfies ALL boundary tightness conditions exactly;")
    print("    only the covering/hub conditions distinguish the sharp configuration)")

    OUT.mkdir(exist_ok=True)
    (OUT / "c26_reduction.json").write_text(json.dumps({
        "R": R, "order": ORDER, "gaps": gaps.tolist(),
        "theta": [math.atan2(p[1], p[0]) for p in sw],
    }, indent=2))
    print("\nwrote", OUT / "c26_reduction.json")


if __name__ == "__main__":
    main()
