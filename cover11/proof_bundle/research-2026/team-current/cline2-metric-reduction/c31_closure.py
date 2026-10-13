"""C31: clean closure audit (supersedes C17/C30 printouts; fixes index conventions).

Conventions
  ring site i  (i = 0..8) with switch order:  switch i = P_i
  site i lies between P_(i-1) and P_i
  gap_i = angle(P_{i-1}, P_i) = owned arc angular width of site i  (LEAD: equal by
          construction; we verify numerically)
  sector angle at site i :  alpha_i = angle at c_i between P_(i-1) and P_i
  base angles of the sector triangle: T_i at P_(i-1), L_i at P_i
  switch angle 2 b_i : angle at P_i in the site triangle (P_i, c_i, c_(i+1))

Exact statements tested:
  A1  T_i + L_i + alpha_i = pi                       (triangle)
  A2  angle of the switch polygon at P_i = pi - (gap_i + gap_(i+1))/2   (= 7pi total)
  A3  closure row  T_i + L_(i+1) + 2 b_i + (gap_i + gap_(i+1))/2 - pi = 0 ?
  A4  sum over i of (A3) : algebraically equals
        3*pi - sum(alpha_i) - sum(2 b_i)   (derived by adding the six named angles
        per switch: for each switch, three triangles contribute T, L and 2b)
  A5  the three-triangle count identity  sum_i (T_i + L_i) + sum_i 2 b_i = 0
"""
import json, math
from pathlib import Path
import numpy as np

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
pi = math.pi
ORDER = [7, 1, 8, 6, 4, 9, 10, 3, 5]


def load():
    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


def ang(V, A, B):
    u = A - V
    w = B - V
    return math.acos(np.clip(u @ w / (np.hypot(*u) * np.hypot(*w)), -1, 1))


def main():
    C = load()
    R = 0.37998385311983884
    sw = []
    for i in range(9):
        s, s2 = ORDER[i], ORDER[(i + 1) % 9]
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
    sw = np.array(sw)

    # gap_i = angle between the two switches of site i, with site i between them.
    # switch index k bounds site k (right) and site k+1 (left)  => gap_i = angle(P_{i-1}, P_i)
    gap = np.array([math.acos(np.clip(sw[(i - 1) % 9] @ sw[i], -1, 1)) for i in range(9)])
    print("gap_i = angle(P_(i-1),P_i)  (deg):", np.round(np.degrees(gap), 6).tolist())
    print("sum gap =", sum(gap), " 2pi =", 2 * pi)

    T = np.zeros(9); L = np.zeros(9); b2 = np.zeros(9); alpha = np.zeros(9)
    for i in range(9):
        c = C[ORDER[i]]
        pL = sw[(i - 1) % 9]
        pR = sw[i]
        T[i] = ang(pL, c, pR)
        L[i] = ang(pR, c, pL)
        alpha[i] = ang(c, pL, pR)
        b2[i] = ang(pR, c, C[ORDER[(i + 1) % 9]])

    print("\nA1: T_i + L_i + alpha_i - pi (should be 0):",
          [f"{x:+.2e}" for x in (T + L + alpha - pi)])

    print("\nA2: switch polygon interior angles")
    ip = pi - (gap + np.roll(gap, -1)) / 2
    print("   per switch (deg):", np.round(np.degrees(ip), 6).tolist())
    print("   sum =", sum(ip), " 7pi =", 7 * pi)

    print("\nA3: closure rows C_i = T_i + L_(i+1) + 2b_i + (gap_i+gap_(i+1))/2 - pi")
    Ci = T + np.roll(L, -1) + b2 + (gap + np.roll(gap, -1)) / 2 - pi
    print("   per site (rad):", [f"{x:+.6e}" for x in Ci])
    print("   max|C| =", max(abs(Ci)), "  sum C =", sum(Ci))

    print("\nA4/A5: the algebraic sum of the closure rows")
    print("   sum_i (T_i + L_i + 2b_i) =", sum(T + L + b2))
    print("   sum_i (gap_i + gap_(i+1))/2 = 2pi (tau) =", sum((gap + np.roll(gap, -1)) / 2))
    print("   so sum C = sum(T+L+2b) + 2pi - 9pi = sum(T+L+2b) - 7pi")
    print("   sum C =", sum(Ci))
    print("   sum(T+L+2b) - 7pi =", sum(T + L + b2) - 7 * pi)
    print("   [if sum C were 0 we would need sum(T+L+2b) = 7pi; the actual gap is]:",
          sum(T + L + b2) - 7 * pi)

    # each switch receives three angle pieces: T of the site on its right,
    # L of the site on its left, and 2b of the site pair - check that the
    # sum of the three equals the switch polygon interior angle.
    print("\nA6: per-switch identity  2 b_i + L_(i+1) + T_i = pi - (gap_i+gap_(i+1))/2  ??")
    lhs = b2 + np.roll(L, -1) + T
    print("   lhs - rhs :", [f"{x:+.6e}" for x in (lhs - ip)])

    OUT.mkdir(exist_ok=True)
    (OUT / "c31_closure.json").write_text(json.dumps({
        "order": ORDER, "gap": gap.tolist(), "T": T.tolist(), "L": L.tolist(),
        "b2": b2.tolist(), "alpha": alpha.tolist(), "closure": Ci.tolist(),
    }, indent=2))
    print("\nwrote", OUT / "c31_closure.json")


if __name__ == "__main__":
    main()
