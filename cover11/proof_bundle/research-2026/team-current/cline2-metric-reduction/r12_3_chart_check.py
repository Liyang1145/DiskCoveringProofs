"""R12-3: independent check of lead/FLAT-PATCH-ARC-CHART.md.

Checks performed (all numeric/structural, no claims):
  (1) the two closed forms  cross(c1,P1) = -r cos(2b+phi)  with phi = asin r,
      and  D = c1.P1 = s^2 - 2 s r sin b cos b + 2 r^2 sin^2 b ;
  (2) sign/positivity threshold: cross > 0  <=>  2b + phi < pi/2  <=>  b > acos(r)/2 ;
  (3) inwardness: |c1|^2 - s^2 = 4 r sin b (r sin b - s cos b) <= 0  <=>  b <= acos r ;
  (4) non-emptiness of the window: acos(r)/2 < acos(r) for r in (0,1), and the
      interval [g, W] with W = 2 atan2(X, D) — is W >= g where g = 2pi - 16 asin(R0)?
      (reported with the lead's R0 = 19/50 convention: g = 2pi - 16 asin(0.38))
  (5) the claimed dichotomy: P1 is the clockwise (ccw) end of c1's covered arc
      exactly when cross(c1,P1) > 0; if cross < 0 the arc lies on the other side
      and the "immediately before P1 clockwise" reading fails.
  (6) alpha1 in (0,pi] and the u1 = |P0-c1| recovery at the window endpoints.
"""
import math
import numpy as np

R0 = 0.38
G = 2 * math.pi - 16 * math.asin(R0)


def c1_of(r, b):
    s = math.sqrt(1 - r * r)
    return np.array([s - 2 * r * math.sin(b) * math.cos(b), -2 * r * math.sin(b) ** 2]), s


def main():
    print("(1) closed forms: cross and D")
    wc = wd = 0.0
    for r in (0.38, 0.4, 0.45, 0.49):
        phi = math.asin(r)
        for b in np.linspace(0.05, math.pi / 2 - 0.05, 97):
            c1, s = c1_of(r, b)
            P1 = np.array([s, -r])
            X = c1[0] * P1[1] - c1[1] * P1[0]
            D = float(c1 @ P1)
            Xf = -r * math.cos(2 * b + phi)
            Df = s * s - 2 * s * r * math.sin(b) * math.cos(b) + 2 * r * r * math.sin(b) ** 2
            wc = max(wc, abs(X - Xf))
            wd = max(wd, abs(D - Df))
    print("    max |cross - (-r cos(2b+phi))| =", wc)
    print("    max |D - closed form|         =", wd)

    print("\n(2) cross > 0  <=>  b > acos(r)/2   (all r)")
    bad = 0
    for r in np.linspace(0.05, 0.95, 19):
        bstar = math.acos(r) / 2
        for b in np.linspace(1e-3, math.pi / 2 - 1e-3, 501):
            c1, s = c1_of(r, b)
            P1 = np.array([s, -r])
            X = c1[0] * P1[1] - c1[1] * P1[0]
            if (X > 1e-14) != (b > bstar + 1e-12):
                bad += 1
    print("    mismatches:", bad)

    print("\n(3) inwardness |c1|^2 <= s^2  <=>  b <= acos r")
    bad3 = 0
    for r in np.linspace(0.05, 0.95, 19):
        bmax = math.acos(r)
        for b in np.linspace(1e-3, math.pi / 2 - 1e-3, 501):
            c1, s = c1_of(r, b)
            inn = float(c1 @ c1) - s * s
            if (inn <= 1e-12) != (b <= bmax + 1e-12):
                bad3 += 1
    print("    mismatches:", bad3)
    print("    identity check  |c1|^2-s^2 = 4 r sin b (r sin b - s cos b):")
    worst = 0.0
    for r in (0.38, 0.45):
        for b in np.linspace(0.1, 1.4, 40):
            c1, s = c1_of(r, b)
            worst = max(worst, abs((float(c1 @ c1) - s * s)
                                   - 4 * r * math.sin(b) * (r * math.sin(b) - s * math.cos(b))))
    print("      max deviation:", worst)

    print("\n(4) window non-emptiness and W vs the uniform floor g")
    print("    g = 2pi - 16 asin(0.38) =", G, "=", math.degrees(G), "deg")
    print("    r     acos(r)/2   acos r    nonempty?   W at b=acos(r)      W at b=acos r")
    for r in (0.38, 0.4, 0.45, 0.49):
        lo = math.acos(r) / 2
        hi = math.acos(r)
        c1a, s = c1_of(r, lo + 1e-9)
        P1 = np.array([s, -r])
        Wa = 2 * math.atan2(c1a[0] * P1[1] - c1a[1] * P1[0], float(c1a @ P1))
        c1b, s = c1_of(r, hi - 1e-9)
        Wb = 2 * math.atan2(c1b[0] * P1[1] - c1b[1] * P1[0], float(c1b @ P1))
        print(f"    {r:.2f}  {math.degrees(lo):8.4f}  {math.degrees(hi):8.4f}   {lo < hi}"
              f"      {math.degrees(Wa):10.5f} deg     {math.degrees(Wb):10.5f} deg")

    print("\n(5) orientation: is P1 the clockwise end exactly when cross > 0?")
    for r, b in ((0.38, 0.3), (0.38, 0.8), (0.38, 1.1), (0.45, 1.3)):
        c1, s = c1_of(r, b)
        P1 = np.array([s, -r])
        X = c1[0] * P1[1] - c1[1] * P1[0]
        print(f"    r={r} b={b:.2f}: cross={X:+.6f} (>0: {X>0})  |c1|={np.hypot(*c1):.6f} s={s:.6f}"
              f"  inward={np.hypot(*c1)<=s+1e-12}")

    print("\n(6) endpoint recovery: W is where both endpoint distances equal r")
    for r, b in ((0.38, 0.6), (0.45, 0.8)):
        c1, s = c1_of(r, b)
        P1 = np.array([s, -r])
        X = c1[0] * P1[1] - c1[1] * P1[0]
        D = float(c1 @ P1)
        W = 2 * math.atan2(X, D)
        th1 = math.atan2(P1[1], P1[0])
        P0 = np.array([math.cos(th1 + W), math.sin(th1 + W)])   # counter-clockwise from P1
        print(f"    r={r} b={b}: W={math.degrees(W):.5f} deg  |P1-c1|={np.hypot(*(P1-c1)):.12f}"
              f"  |P0-c1|={np.hypot(*(P0-c1)):.12f}  (both should equal r={r})")
        # with the OPPOSITE orientation
        P0b = np.array([math.cos(th1 - W), math.sin(th1 - W)])
        print(f"        opposite orientation: |P0-c1| = {np.hypot(*(P0b-c1)):.6f}")


if __name__ == "__main__":
    main()
