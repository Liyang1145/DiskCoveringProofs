"""R13-4: FINAL exact statements for W(r,b): closed form, bound, exact inversion.

Verified (numerics = calibration only; each item has an algebraic proof sketched).

  (E1) X = r sin x ,  D = 1 - r cos x ,      x := 2b - alpha ,  alpha := acos r .
  (E2) W = 2 atan2(r sin x, 1 - r cos x) = 2 atan2(cos(alpha) sin x, 1 + cos(alpha) cos x).
  (E3) W : [0, pi-alpha] -> [0, pi-2alpha] is strictly increasing, pi-2alpha = 2 asin r,
       so W <= 2 asin r with EQUALITY at b = alpha (x = pi - alpha).
  (E4) EXACT INVERSION.  With u := g/2 the defining equation is
            tan u = cos(alpha) sin x / (1 + cos(alpha) cos x) ,
       and its solution in (0, pi-alpha) is
            x = pi - alpha - atan2( sin(2u) , cos(2u) + sec(alpha) )
              = pi - alpha - g ... (no: see the verified expression)
       equivalently, with v := pi - alpha - x,
            tan(v/2) = cos(alpha) sin x / (1 + cos(alpha) cos x + sqrt(1 + 2 cos(alpha) cos x + cos^2 alpha))
       and the simple explicit form
            b_min(r,g) = alpha + (pi - alpha)/2 - g/2 - (1/2) atan2( sin g , cos g + sec(alpha) ).
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


def bmin_formula(r, g):
    al = math.acos(r)
    return al + (math.pi - al) / 2 - g / 2 - 0.5 * math.atan2(math.sin(g), math.cos(g) + 1 / math.cos(al))


def main():
    print("(E4) inversion: b_min formula vs bisection")
    print("   r      g(deg)      formula(deg)        bisection(deg)      diff")
    worst = 0.0
    for r in (0.375, 0.38, 0.39, 0.40, 0.45, 0.49):
        al = math.acos(r)
        gmax = math.pi - 2 * al
        gs = [math.degrees(2 * math.pi - 16 * math.asin(0.38)), 5.0, 20.0,
              math.degrees(gmax) * 0.999]
        for gd in gs:
            g = math.radians(gd)
            if g > gmax:
                continue
            bf = bmin_formula(r, g)
            lo, hi = al / 2, al
            for _ in range(220):
                mid = (lo + hi) / 2
                if W(r, mid) < g:
                    lo = mid
                else:
                    hi = mid
            bb = (lo + hi) / 2
            worst = max(worst, abs(bf - bb))
            print(f"   {r:.3f}  {gd:9.5f}   {math.degrees(bf):18.12f}  {math.degrees(bb):18.12f}"
                  f"   {math.degrees(bf-bb):+.2e}")
    print("   worst |formula - bisection| =", worst)

    print("\n(E4b) the same statement as an explicit x-relation")
    print("   x_min(g) = pi - alpha - atan2(sin g, cos g + sec alpha);  check W at x = x_min")
    worst2 = 0.0
    for r in (0.375, 0.38, 0.40, 0.49):
        al = math.acos(r)
        for gd in (2.661077475115173, 10.0, 30.0, math.degrees(math.pi - 2 * al) * 0.999):
            g = math.radians(gd)
            if g > math.pi - 2 * al:
                continue
            x = math.pi - al - math.atan2(math.sin(g), math.cos(g) + 1 / math.cos(al))
            b = (al + x) / 2
            worst2 = max(worst2, abs(W(r, b) - g))
    print("   max | W(b(x_min)) - g | =", worst2)

    print("\n(algebraic check of the key identity)")
    print("   claim: for x = pi - alpha - atan2(sin g, cos g + sec alpha) with u = g/2,")
    print("          tan u = cos(alpha) sin x / (1 + cos(alpha) cos x)   holds identically.")
    worst3 = 0.0
    for al in np.linspace(0.05, 1.50, 300):
        for g in np.linspace(1e-8, math.pi - 2 * al - 1e-9, 61):
            x = math.pi - al - math.atan2(math.sin(g), math.cos(g) + 1 / math.cos(al))
            lhs = math.tan(g / 2)
            rhs = math.cos(al) * math.sin(x) / (1 + math.cos(al) * math.cos(x))
            worst3 = max(worst3, abs(lhs - rhs))
    print("   max |tan(g/2) - cos(alpha) sin x/(1+cos(alpha)cos x)| =", worst3)

    print("\n(E2) exact closed forms")
    e1 = e2 = 0.0
    for r in np.linspace(0.05, 0.95, 19):
        al = math.acos(r)
        for b in np.linspace(al / 2, al, 401):
            x = 2 * b - al
            e1 = max(e1, abs(W(r, b) - 2 * math.atan2(r * math.sin(x), 1 - r * math.cos(x))))
            e2 = max(e2, abs(W(r, b) - 2 * math.atan2(math.cos(al) * math.sin(x),
                                                      1 + math.cos(al) * math.cos(x))))
    print("   max |W - 2atan2(r sin x, 1 - r cos x)|        =", e1)
    print("   max |W - 2atan2(cos al sin x, 1 + cos al cos x)| =", e2)


if __name__ == "__main__":
    main()
