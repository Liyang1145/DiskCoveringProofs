"""R12-5: why W = 2 atan2(X,D) is the arc width; orientation of P1; alpha branch.

For c1 with |P1 - c1| = r, P1 on the unit circle, put
    D = c1.P1 = |c1| cos(delta),  X = cross(c1,P1) = |c1| sin(delta),
    delta = angle(c1, P1).
Then:
    D = (1 + |c1|^2 - r^2)/2        (*  from |P1-c1|^2 = r^2)
    the covered arc = {x : |x|=1, |x-c1| <= r} has
        half-width Delta_max = arccos( min(1, |c1| (1 - r^2)/( (1+|c1|^2) ... )) )
    and in fact  Delta_max = delta  (checked below), so the width is W = 2 delta.
Checks: (i) Delta_max = delta; (ii) P1 is the counter-clockwise end iff X>0;
(iii) alpha1 = angle(P0-c1, P1-c1) and u1 = |P0-c1| at the two window ends.
"""
import math
import numpy as np


def build(r, b):
    s = math.sqrt(1 - r * r)
    c1 = np.array([s - 2 * r * math.sin(b) * math.cos(b), -2 * r * math.sin(b) ** 2])
    return c1, np.array([s, -r]), s


def arc_halfwidth(r, c1):
    """half angular width of {|x|=1, |x-c1|<=r}: solve 1+|c1|^2-2|c1|cos = r^2"""
    n = float(np.hypot(*c1))
    v = (1 + n * n - r * r) / (2 * n)
    v = min(1.0, max(-1.0, v))
    return math.acos(v)


def main():
    print("(i) Delta_max (arc half-width) vs delta = angle(c1,P1)")
    worst = 0.0
    for r in (0.38, 0.45, 0.49):
        for bd in np.linspace(math.degrees(math.acos(r) / 2) + 0.5, 89.5, 40):
            b = math.radians(bd)
            c1, P1, s = build(r, b)
            if float(np.hypot(*c1)) <= 1e-12:
                continue
            dmax = arc_halfwidth(r, c1)
            delta = math.atan2(c1[0] * P1[1] - c1[1] * P1[0], float(c1 @ P1))
            worst = max(worst, abs(dmax - delta))
    print("    max |Delta_max - delta| =", worst, "  (so W = 2delta = 2Delta_max)")

    print("\n(ii) orientation: shell of P1 relative to the arc centre direction")
    print("     r     b(deg)   X          2delta=W(deg)  ang(P1)-ang(c1) (deg)   P1 at which end")
    for r in (0.38, 0.45):
        for bd in (40, 60, 70, 80):
            b = math.radians(bd)
            c1, P1, s = build(r, b)
            X = c1[0] * P1[1] - c1[1] * P1[0]
            D = float(c1 @ P1)
            W = 2 * math.atan2(X, D)
            d1 = math.degrees(math.atan2(P1[1], P1[0]))
            dc = math.degrees(math.atan2(c1[1], c1[0]))
            diff = (d1 - dc + 180) % 360 - 180
            end = "ccw (+Delta)" if X > 0 else "cw (-Delta)"
            print(f"    {r:.2f}  {bd:4d}   {X:+.6f}   {math.degrees(W):10.5f}     {diff:10.5f}"
                  f"            {end}")

    print("\n(iii) window ends: P0 at w1 = 0 (coincides with P1) and w1 = W")
    for r, b in ((0.38, 1.0), (0.45, 0.9)):
        c1, P1, s = build(r, b)
        X = c1[0] * P1[1] - c1[1] * P1[0]
        D = float(c1 @ P1)
        W = 2 * math.atan2(X, D)
        th1 = math.atan2(P1[1], P1[0])
        for tag, w in (("w=0", 0.0), ("w=W", W), ("w=W/2", W / 2)):
            P0 = np.array([math.cos(th1 - w), math.sin(th1 - w)])   # clockwise from P1
            u1 = float(np.hypot(*(P0 - c1))) / r
            a1 = math.degrees(math.acos(np.clip(
                (P0 - c1) @ (P1 - c1) / (np.hypot(*(P0 - c1)) * np.hypot(*(P1 - c1))), -1, 1)))
            print(f"    r={r} b={b}: {tag}: |P0-c1|/r = {u1:.9f}   alpha1 = {a1:.5f} deg")


if __name__ == "__main__":
    main()
