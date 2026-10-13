"""R13-2: exact closed form, bound, and inversion for the arc width W.

Setup: r in (0,1), s = sqrt(1-r^2), alpha = acos r, x := 2b - alpha in [0, pi-alpha].
        c1 = (s - 2r sin b cos b, -2r sin^2 b),  P1 = (s,-r),
        X = cross(c1,P1), D = c1.P1, W = 2 atan2(X,D).

Exact identities verified here (no sampling used as proof; numerics are calibration):
  (i)   X = r sin x ,   D = 1 - r cos x            [two-line trig identity]
  (ii)  W = 2 atan2( r sin x , 1 - r cos x )
        = 2 atan2( cos(alpha) sin x , 1 + cos(alpha) cos x )
        = 2 atan2( sin v , cos v + sec alpha ) with v := pi - alpha - x
  (iii) W(b) increases from 0 (x=0) to pi-2 alpha (x=pi-alpha) = 2 asin r
        => W <= 2 asin r, equality at b = alpha (the inwardness end)
  (iv)  W = g  <=>  x = g  <=>  b_min(r,g) = (alpha + g)/2 , valid for
        0 <= g <= pi - 2 alpha ; at r = 0.38 the range is [0, 44.66737 deg] and
        the floor g0 = 2pi - 16 asin(0.38) = 2.661077 deg lies inside.
"""
import math
import numpy as np


def XD(r, b):
    s = math.sqrt(1 - r * r)
    c1 = np.array([s - 2 * r * math.sin(b) * math.cos(b), -2 * r * math.sin(b) ** 2])
    P1 = np.array([s, -r])
    return c1[0] * P1[1] - c1[1] * P1[0], float(c1 @ P1)


def W(r, b):
    X, D = XD(r, b)
    return 2 * math.atan2(X, D)


def main():
    print("(i) X = r sin x, D = 1 - r cos x   (x = 2b - alpha)")
    w1 = w2 = 0.0
    for r in np.linspace(0.02, 0.98, 49):
        al = math.acos(r)
        for b in np.linspace(al / 2, al, 61):
            x = 2 * b - al
            X, D = XD(r, b)
            w1 = max(w1, abs(X - r * math.sin(x)))
            w2 = max(w2, abs(D - (1 - r * math.cos(x))))
    print("   max |X - r sin x| =", w1, "  max |D - 1 + r cos x| =", w2)

    print("\n(ii) three equivalent closed forms")
    e1 = e2 = 0.0
    for r in np.linspace(0.05, 0.95, 19):
        al = math.acos(r)
        ca, sa = math.cos(al), math.sin(al)
        for b in np.linspace(al / 2, al, 401):
            x = 2 * b - al
            f1 = 2 * math.atan2(r * math.sin(x), 1 - r * math.cos(x))
            f2 = 2 * math.atan2(ca * math.sin(x), 1 + ca * math.cos(x))
            e1 = max(e1, abs(W(r, b) - f1))
            e2 = max(e2, abs(W(r, b) - f2))
    print("   max |W - 2 atan2(r sin x, 1 - r cos x)|        =", e1)
    print("   max |W - 2 atan2(cos al sin x, 1 + cos al cos x)| =", e2)

    print("\n(iii) monotonicity and the bound W <= 2 asin r")
    print("   r      W at b=alpha/2   W at b=alpha     pi-2alpha     2 asin r     monotone on a fine grid")
    for r in (0.375, 0.38, 0.40, 0.45, 0.49):
        al = math.acos(r)
        bs = np.linspace(al / 2, al, 20001)
        Ws = np.array([W(r, b) for b in bs])
        mono = bool(np.all(np.diff(Ws) >= -1e-13))
        print(f"   {r:.3f}  {math.degrees(Ws[0]):13.6f}  {math.degrees(Ws[-1]):14.6f}"
              f"  {math.degrees(math.pi-2*al):12.6f}  {math.degrees(2*math.asin(r)):11.6f}   {mono}")

    print("\n(iv) inversion: W = g  <=>  b = (alpha+g)/2")
    worst = 0.0
    for r in (0.375, 0.38, 0.40, 0.45, 0.49):
        al = math.acos(r)
        gmax = math.pi - 2 * al
        for gd in (2.661077475115173, 5.0, 20.0, math.degrees(gmax) - 1e-6):
            g = math.radians(gd)
            if g > gmax:
                continue
            bf = (al + g) / 2
            lo, hi = al / 2, al
            for _ in range(200):
                mid = (lo + hi) / 2
                if W(r, mid) < g:
                    lo = mid
                else:
                    hi = mid
            bb = (lo + hi) / 2
            worst = max(worst, abs(bf - bb))
            print(f"   r={r:.3f} g={gd:8.4f} deg -> formula {math.degrees(bf):.10f} deg"
                  f"   bisection {math.degrees(bb):.10f} deg   diff {math.degrees(bf-bb):+.2e}")
    print("   worst |formula - bisection| =", worst)

    print("\n(v) the floor is inside the range at the radii of interest")
    g0 = 2 * math.pi - 16 * math.asin(0.38)
    for r in (0.375, 0.38, 0.39, 0.40):
        al = math.acos(r)
        print(f"   r={r}: g0 = {math.degrees(g0):.6f} deg <= pi-2alpha = "
              f"{math.degrees(math.pi-2*al):.6f} deg : {g0 <= math.pi-2*al};"
              f"  b_min = {math.degrees((al+g0)/2):.6f} deg, alpha = {math.degrees(al):.6f} deg,"
              f"  nonempty: {(al+g0)/2 <= al}")

    print("\n(vi) the correct 'v' form: define v by x = pi - alpha - v; then")
    print("     tan(v/2)... check  tan((pi-alpha-x)/2) vs the half-angle identity")
    for r, bd in ((0.38, 60.0), (0.45, 50.0)):
        al = math.acos(r)
        b = math.radians(bd)
        x = 2 * b - al
        v = math.pi - al - x
        lhs = math.tan(v / 2)
        rhs = math.cos(al) * math.sin(x) / (1 + math.cos(al) * math.cos(x) + math.sqrt(1 + 2 * math.cos(al) * math.cos(x) + math.cos(al) ** 2))
        print(f"   r={r} b={bd}: tan(v/2)={lhs:.12f}  closed form={rhs:.12f}  diff={lhs-rhs:+.2e}")


if __name__ == "__main__":
    main()
