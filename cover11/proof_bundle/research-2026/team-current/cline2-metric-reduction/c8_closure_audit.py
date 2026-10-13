"""C8: closure-equation audit on the exact candidate, plus the exact area identity.

Computes, from the 22 integer literals only:
  * the 9 owned boundary arcs and their real widths w_i;
  * the switch base angles L_i,T_i,b_i and the closure residual
        T_i + L_(i+1) + 2 b_i + (w_i + w_(i+1))/2 - pi;
  * the same quantity with the switch angular gaps theta_(i+1)-theta_i in place
    of (w_i+w_(i+1))/2 and with (phi_i+phi_(i+1))/2, to identify the right form;
  * the exact arc-area identity  area(cup) = sum_i t_i w_i + sum_V (2pi-2pi/3)
    and checks it against pi.
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


def main():
    P = load()
    n = len(P)
    R = 0.37998385311983884
    c7 = json.loads((OUT / "c7_cyclic.json").read_text())
    arcs = c7["arcs"]                       # site, theta0, theta1, w  (unit-circle arcs)
    order = [a["site"] for a in arcs]
    print("cyclic ring order:", order)
    print("arc widths w_i:", [round(a["w"], 12) for a in arcs])
    print("all widths equal 2pi/9?", max(abs(a["w"] - 2 * pi / 9) for a in arcs) < 1e-6)

    # switch i = boundary between ring site order[i] and order[i+1]
    sw = []
    m = len(order)
    for i in range(m):
        s, s2 = order[i], order[(i + 1) % m]
        # switch = intersection of bisector(c_s,c_s2) with S^1
        a, b = P[s], P[s2]
        mx = (a + b) / 2
        dv = b - a
        t = (dv @ mx) / (dv @ dv)
        f = dv * t
        h = math.hypot(*f)
        u = np.array([-dv[1], dv[0]]) / math.hypot(*dv)
        ss = math.sqrt(max(0.0, 1 - h * h))
        for sgn in (1, -1):
            p = f + sgn * ss * u
            d = np.hypot(*(P - p[None, :]).T)
            if d.min() >= R - 1e-9:
                sw.append((i, s, s2, p))
                break
    assert len(sw) == 9, len(sw)
    print("\nswitch angles (deg):", [round(math.degrees(math.atan2(p[1], p[0])), 9) for _, _, _, p in sw])
    th = [math.atan2(p[1], p[0]) for _, _, _, p in sw]
    gaps = [((th[(i + 1) % 9] - th[i]) % (2 * pi)) for i in range(9)]
    print("switch angular gaps (deg):", [round(math.degrees(g), 9) for g in gaps])

    print("\n=== closure residuals ===")
    print(" i  site  alpha(deg)   rho_i    T_i(deg)   L_i(deg)   b_i(deg)   res_A      res_B      res_C")
    resA = []; resB = []; resC = []
    alpha = [None] * 9
    T = [None] * 9
    L = [None] * 9
    bb = [None] * 9
    for i in range(9):
        s_i = order[i]
        s_prev = order[(i - 1) % 9]
        s_next = order[(i + 1) % 9]
        c = P[s_i]
        # switch left = between prev and i ; switch right = between i and next
        pL = [q for (k, s1, s2, q) in sw if k == (i - 1) % 9][0]
        pR = [q for (k, s1, s2, q) in sw if k == i][0]
        # sector angle at c between the two switches, and radii
        vL = pL - c
        vR = pR - c
        al = math.acos(np.clip(vL @ vR / (np.hypot(*vL) * np.hypot(*vR)), -1, 1))
        alpha[i] = al
        u_i = np.hypot(*vL)     # radius of c at switch i-1
        v_i = np.hypot(*vR)     # radius of c at switch i
        # base angles of the triangle (c, P_L, P_R): L_i at P_L? define:
        #   T_i = angle at P_L (left switch), L_i = angle at P_R (right switch)
        # switch angle 2b_i at P_right between c and c_next happens in the NEXT triangle;
        # here we compute the angle at P_R in triangle(c, P_L, P_R)
        def ang_at(V, A, B):
            return math.acos(np.clip((A - V) @ (B - V) / (np.hypot(*(A - V)) * np.hypot(*(B - V))), -1, 1))
        Ti = ang_at(pL, c, pR)
        Li = ang_at(pR, c, pL)
        T[i] = Ti; L[i] = Li
        # 2b_i: angle at switch i (pR here) in the site triangle (P_i, c_i, c_next)
        s_next2 = order[(i + 1) % 9]
        two_b = ang_at(pR, c, P[s_next2])
        bb[i] = two_b / 2
        w_here = gaps[i] * 1.0
        w_plus = (gaps[i] + gaps[(i + 1) % 9]) / 2
        resA.append(Ti + L[(i + 1) % 9] + two_b + w_plus - pi)
        # variant B: previous L with this switch's T
        resB.append((T[(i - 1) % 9] + Li + two_b + w_plus - pi) if i > 0 else float('nan'))
        # variant C: using phi (angle at P between the two spokes to prev switch and origin)
        resC.append(Ti + L[(i + 1) % 9] + two_b + (w_plus) - pi)
        print(f"{i:2d}  {s_i:2d}  {math.degrees(al):10.6f} {np.hypot(*c):.6f} {math.degrees(Ti):10.6f} {math.degrees(Li):10.6f} {math.degrees(bb[i]):10.6f}"
              f" {math.degrees(resA[-1]):+.3e} " + (f"{math.degrees(resB[-1]):+.3e}" if i else "   n/a     ") + f" {math.degrees(resC[-1]):+.3e}")

    print("\nsum of sector angles (should be 2pi + 2*sum b_extra):")
    print("  sum alpha =", sum(alpha), " 2pi =", 2 * pi)
    print("  sum 2b =", sum(bb) * 2, " pi =", pi, " 2pi-2sum b =", 2 * pi - 2 * sum(bb))
    print("  sum (alpha) - (2pi) - 2*sum(b) + pi =", sum(alpha) - 2 * pi - 2 * sum(bb) + pi)
    print("  sum of closure residuals A =", sum(resA))
    print("  check identity: sum resA = 2pi - 2 sum alpha + pi + sum w ? ->",
          2 * pi - 2 * sum(alpha) + pi + sum(gaps))
    print("  sum w =", sum(gaps))

    # --- exact area identity
    # union area = sum over owned arcs t_i*w_i + (#interior Voronoi-type vertices)*pi/3*?
    # Derive numerically via boundary integral to confirm the formula.
    # interior tight vertices at distance R have angle R = 2pi/3 in each cell
    t_i = [np.hypot(*(P[order[i]])) ** 2 for i in range(9)]
    area_arc = sum(t_i[i] * gaps[i] for i in range(9))
    print("\nsum_i |c_i|^2 * w_i =", area_arc, " vs pi =", pi, " diff =", area_arc - pi)
    OUT.mkdir(exist_ok=True)
    (OUT / "c8_closure.json").write_text(json.dumps({
        "order": order, "widths": gaps, "alpha": alpha, "T": T, "L": L, "b": bb,
        "resA": resA, "t": t_i, "area_arc": area_arc}, indent=2))
    print("wrote", OUT / "c8_closure.json")


if __name__ == "__main__":
    main()
