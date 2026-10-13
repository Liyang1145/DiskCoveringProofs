"""R12-4: verify the lead's W = 2 atan2(X, D) against the numerically computed
covered-arc width, and settle the orientation convention.

For c1 = (s - 2r sin b cos b, -2r sin^2 b), P1 = (s,-r), X = cross(c1,P1),
D = c1.P1, the claim is that the full width of {x on |x|=1 : |x-c1| <= r} -- the
angular measure of the arc -- equals W = 2 atan2(X,D).

We measure the arc directly and also test the two candidate formulas
   W_angle = 2 * angle(c1, P1)         (= the lead's W)
   W_chord = 2 * arcsin( (2 r sin b)/2 )  ... etc,
then determine which endpoint P1 is (clockwise or counter-clockwise) by checking
the sign of X.
"""
import math
import numpy as np

def build(r, b):
    s = math.sqrt(1 - r * r)
    c1 = np.array([s - 2 * r * math.sin(b) * math.cos(b), -2 * r * math.sin(b) ** 2])
    P1 = np.array([s, -r])
    return c1, P1, s

def measure_arc(r, b, n=4000000):
    c1, P1, s = build(r, b)
    if np.hypot(*c1) <= r * 0 + 1e-15:
        return None
    t = np.linspace(0, 2 * math.pi, n + 1)[:-1]
    X = np.stack([np.cos(t), np.sin(t)], 1)
    d = np.hypot(X[:, 0] - c1[0], X[:, 1] - c1[1])
    inside = d <= r
    if not inside.any():
        return None
    # angular measure of the inside set (contiguous)
    idx = np.where(inside)[0]
    return len(idx) * (2 * math.pi / n), t, inside

def main():
    print("r     b(deg)   |c1|      s        X          W_lead(deg)  arc measured(deg)   2b(deg)   140*b?"
          "  ccw/clockwise")
    for r in (0.38, 0.45):
        s = math.sqrt(1 - r * r)
        for bd in (20, 40, 60, 70, 80, 85, 89):
            b = math.radians(bd)
            c1, P1, s2 = build(r, b)
            X = c1[0] * P1[1] - c1[1] * P1[0]
            D = float(c1 @ P1)
            if X <= 0:
                print(f"{r:.2f}  {bd:4d}   {np.hypot(*c1):.6f}  {s2:.6f}  {X:+.6f}   X<=0 -> arc not on this side")
                continue
            W = 2 * math.atan2(X, D)
            m = measure_arc(r, b, n=1500000)
            arc = m[0] if m else float('nan')
            print(f"{r:.2f}  {bd:4d}   {np.hypot(*c1):.6f}  {s2:.6f}  {X:+.6f}   {math.degrees(W):10.5f}"
                  f"   {math.degrees(arc):10.5f}     {math.degrees(2*b):8.4f}   {X>0}")
    print("\nIs W (lead) equal to the measured arc width? (per-row comparison above)")


if __name__ == "__main__":
    main()
