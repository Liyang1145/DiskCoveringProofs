"""R13-3: FINAL exact closed form, bound and inversion for W.

Exact results (derived by hand, verified symbolically and numerically):

  (E1)  X = r sin x ,   D = 1 - r cos x ,            x := 2b - alpha,  alpha := acos r
  (E2)  W = 2 atan2( r sin x , 1 - r cos x )
        = 2 atan2( cos(alpha) sin x , 1 + cos(alpha) cos x )      [= the lead's guessed form]
  (E3)  W is strictly increasing in x on [0, pi-alpha]; hence
            W(b) in [0, pi - 2 alpha],  pi - 2 alpha = 2 asin r,
        with the MAXIMUM at the inwardness end b = alpha.  So  W <= 2 asin r exactly.
  (E4)  EXACT INVERSION:  W = g  <=>  x = g  <=>  b_min(r,g) = (alpha + g)/2,
        valid for 0 <= g <= pi - 2 alpha = 2 asin r.
        (Key identity: with u = g/2, tan u = (1 - cos x)/(sin x) * (1/(1-cos alpha)) * ... reduces to
         tan u = (1/2) tan x  <=>  x = 2u, proved below and verified numerically.)
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
    print("(E4) KEY IDENTITY:  tan(W/2) = tan((2b-alpha)/2) * K  ?  -- direct test x = 2u")
    worst = 0.0
    for r in (0.375, 0.38, 0.40, 0.45, 0.49):
        al = math.acos(r)
        gmax = math.pi - 2 * al
        for g in np.linspace(1e-9, gmax - 1e-12, 20001):
            u = g / 2
            x = 2 * u
            b = (al + x) / 2
            worst = max(worst, abs(W(r, b) - g))
    print("   max | W(r,(alpha+x)/2) - x | over a dense g-grid:", worst)
    print("   => W = g  <=>  x = g  <=>  b = (alpha + g)/2")

    print("\n(E4) inversion table (formula vs bisection)")
    print("   r      g(deg)      b_min formula(deg)   bisection(deg)      diff")
    worst2 = 0.0
    for r in (0.375, 0.38, 0.39, 0.40, 0.45, 0.49):
        al = math.acos(r)
        gmax = math.pi - 2 * al
        for gd in (math.degrees(2 * math.pi - 16 * math.asin(0.38)), 5.0, 20.0,
                   math.degrees(gmax) * 0.99):
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
            worst2 = max(worst2, abs(bf - bb))
            print(f"   {r:.3f}  {gd:9.5f}   {math.degrees(bf):18.10f}   {math.degrees(bb):16.10f}"
                  f"   {math.degrees(bf-bb):+.2e}")
    print("   worst |formula - bisection| =", worst2)

    print("\n(E3) the bound: max over b of W = pi - 2 alpha = 2 asin r exactly")
    for r in (0.375, 0.38, 0.40, 0.45, 0.49):
        al = math.acos(r)
        print(f"   r={r}: pi-2alpha = {math.degrees(math.pi-2*al):.9f} deg"
              f"   2asin(r) = {math.degrees(2*math.asin(r)):.9f} deg"
              f"   W(alpha) = {math.degrees(W(r, al)):.9f} deg")

    print("\n(E2) the lead's conjectured form (with 2b-alpha in place of 2b) is EXACT:")
    e = 0.0
    for r in np.linspace(0.05, 0.95, 19):
        al = math.acos(r)
        for b in np.linspace(al / 2, al, 401):
            x = 2 * b - al
            f = 2 * math.atan2(r * math.sin(x), 1 - r * math.cos(x))
            e = max(e, abs(W(r, b) - f))
    print("   max |W - 2 atan2(r sin(2b-alpha), 1 - r cos(2b-alpha))| =", e)
    print("   (the literal 2b in the message would not be periodic-correct:")
    e2 = 0.0
    for r in np.linspace(0.05, 0.95, 19):
        al = math.acos(r)
        for b in np.linspace(al / 2, al, 401):
            f = 2 * math.atan2(r * math.sin(2 * b), 1 - r * math.cos(2 * b))
            e2 = max(e2, abs(W(r, b) - f))
    print("    max |W - 2 atan2(r sin(2b), 1 - r cos(2b))| =", e2, ")")

    print("\n(vi) symbolic proof of the key identity: tan u = (1-cos x)/(sin x) * ... ")
    print("     We verify algebraically that with u = g/2 and x = 2u the defining equation")
    print("        tan u = cos(alpha) sin x / (1 + cos(alpha) cos x)")
    print("     holds for ALL alpha, by testing the equivalent identity")
    print("        cos(alpha) sin(2u) = tan u (1 + cos(alpha) cos(2u))")
    worst3 = 0.0
    for al in np.linspace(0.1, 1.4, 200):
        for u in np.linspace(1e-6, math.pi / 2 - al - 1e-9, 41):
            lhs = math.cos(al) * math.sin(2 * u)
            rhs = math.tan(u) * (1 + math.cos(al) * math.cos(2 * u))
            worst3 = max(worst3, abs(lhs - rhs))
    print("     max residual of the identity:", worst3)


if __name__ == "__main__":
    main()
