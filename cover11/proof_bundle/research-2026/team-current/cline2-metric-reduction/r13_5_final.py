"""R13-5: FINAL, verified. Exact closed form / bound / inversion for the arc width W.

Definitions
    r in (0,1),  s = sqrt(1-r^2),  alpha := acos r,  phi := asin r  (alpha + phi = pi/2)
    b in [alpha/2, alpha],  x := 2b - alpha  in [0, pi - alpha]
    c1 = (s - 2r sin b cos b, -2r sin^2 b),  P1 = (s,-r)
    X = cross(c1,P1),  D = c1.P1,  W = 2 atan2(X, D)

EXACT STATEMENTS (each proved by the two-line identities displayed in the report):
  (E1) X = r sin x ,  D = 1 - r cos x .
  (E2) W = 2 atan2( r sin x , 1 - r cos x ) .            [closed form]
  (E3) W = 2 u  with  tan u = r sin x / (1 - r cos x) ,  u in [0, asin r] .
  (E4) W is strictly increasing in x, W(0) = 0, W(pi-alpha) = pi - 2 alpha = 2 asin r.
       Hence W <= 2 asin r, with equality exactly at x = pi - alpha (b = alpha).
  (E5) EXACT INVERSION  W = g  <=>  x = x_min(g) where
           tan(g/2) = r sin x_min / (1 - r cos x_min)
       i.e.  x_min = arccos( (r + cos(g/2) sqrt(1 + r^2 - cos^2(g/2))) / (1 + ... ) )
       solved explicitly below, and then  b_min(r,g) = (alpha + x_min)/2 .
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


def x_min_closed(r, g):
    """solve tan(g/2) = r sin x/(1 - r cos x) for x in [0, pi-alpha]:

       t(1 - r cos x) = r sin x         (t := tan(g/2))
       t - tr cos x = r sin x
       write u_ := g/2:  use half-angle  z = tan(x/2)
       t(1 - r(1-z^2)/(1+z^2)) = r 2z/(1+z^2)
       t(1+z^2 - r + r z^2) = 2 r z
       t(1-r) + t(1+r) z^2 - 2 r z = 0
    """
    t = math.tan(g / 2)
    A = t * (1 + r)
    B = -2 * r
    C = t * (1 - r)
    disc = B * B - 4 * A * C
    if disc < 0:
        return None
    z = (-B - math.sqrt(disc)) / (2 * A)          # the small root
    return 2 * math.atan(z)


def main():
    print("(E1) X = r sin x, D = 1 - r cos x")
    w1 = w2 = 0.0
    for r in np.linspace(0.02, 0.98, 49):
        al = math.acos(r)
        for b in np.linspace(al / 2, al, 61):
            x = 2 * b - al
            X, D = XD(r, b)
            w1 = max(w1, abs(X - r * math.sin(x)))
            w2 = max(w2, abs(D - (1 - r * math.cos(x))))
    print("   max residuals:", w1, w2)

    print("\n(E2) closed form  W = 2 atan2(r sin x, 1 - r cos x)")
    e = 0.0
    for r in np.linspace(0.05, 0.95, 19):
        al = math.acos(r)
        for b in np.linspace(al / 2, al, 401):
            x = 2 * b - al
            e = max(e, abs(W(r, b) - 2 * math.atan2(r * math.sin(x), 1 - r * math.cos(x))))
    print("   max residual:", e)

    print("\n(E3)/(E4) u-relation, monotonicity, bound")
    e3 = 0.0
    for r in np.linspace(0.05, 0.95, 19):
        al = math.acos(r)
        for b in np.linspace(al / 2 + 1e-12, al, 401):
            x = 2 * b - al
            e3 = max(e3, abs(math.tan(W(r, b) / 2) - r * math.sin(x) / (1 - r * math.cos(x))))
    print("   max |tan(W/2) - r sin x/(1 - r cos x)| =", e3)
    for r in (0.375, 0.38, 0.40, 0.45, 0.49):
        al = math.acos(r)
        bs = np.linspace(al / 2, al, 20001)
        Ws = np.array([W(r, b) for b in bs])
        print(f"   r={r:.3f}: W -> [{math.degrees(Ws.min()):.9f},{math.degrees(Ws.max()):.9f}] deg"
              f"  monotone={bool(np.all(np.diff(Ws) >= -1e-13))}"
              f"  2asin r = {math.degrees(2*math.asin(r)):.9f} deg")

    print("\n(E5) exact inversion: x_min from the quadratic, then b_min = (alpha + x_min)/2")
    print("   r      g(deg)     x_min(deg)   b_min(deg)   W(b_min) (deg)   |W-g|       bisection check")
    worst = 0.0
    for r in (0.375, 0.38, 0.39, 0.40, 0.45, 0.49):
        al = math.acos(r)
        gmax = math.pi - 2 * al
        for gd in (math.degrees(2 * math.pi - 16 * math.asin(0.38)), 5.0, 20.0,
                   math.degrees(gmax) * 0.999):
            g = math.radians(gd)
            if g > gmax:
                continue
            x = x_min_closed(r, g)
            if x is None:
                print(f"   {r:.3f}  {gd:9.5f}   no real root")
                continue
            b = (al + x) / 2
            Wb = W(r, b)
            lo, hi = x, x
            worst = max(worst, abs(Wb - g))
            print(f"   {r:.3f}  {gd:9.5f}  {math.degrees(x):11.7f}  {math.degrees(b):11.7f}"
                  f"   {math.degrees(Wb):14.9f}   {math.degrees(Wb-g):+.2e}")
    print("   worst |W(b_min) - g| =", worst)

    print("\n   cross-check against bisection on b:")
    worst2 = 0.0
    for r in (0.375, 0.38, 0.40, 0.45, 0.49):
        al = math.acos(r)
        for gd in (math.degrees(2 * math.pi - 16 * math.asin(0.38)), 10.0, 30.0):
            g = math.radians(gd)
            if g > math.pi - 2 * al:
                continue
            xc = x_min_closed(r, g)
            bc = (al + xc) / 2
            lo, hi = al / 2, al
            for _ in range(220):
                mid = (lo + hi) / 2
                if W(r, mid) < g:
                    lo = mid
                else:
                    hi = mid
            bb = (lo + hi) / 2
            worst2 = max(worst2, abs(bc - bb))
            print(f"     r={r:.3f} g={gd:8.4f}: closed {math.degrees(bc):.10f} deg"
                  f"  bisection {math.degrees(bb):.10f} deg  diff {math.degrees(bc-bb):+.2e}")
    print("     worst |closed - bisection| =", worst2)


if __name__ == "__main__":
    main()
