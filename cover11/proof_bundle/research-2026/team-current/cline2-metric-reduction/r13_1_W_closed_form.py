"""R13-1: exact closed form for W, the conjectured atan formula, the bound
W <= 2 asin r, and the inversion for b_min(r,g).

Setup (lead's chart):
  r in (0,1), s = sqrt(1-r^2), phi = asin r, alpha = acos r,
  c1 = (s - 2r sin b cos b, -2r sin^2 b), P1 = (s,-r),
  X = cross(c1,P1) = -r cos(2b+phi),  D = c1.P1,
  W = 2 atan2(X,D).

Candidate closed forms tested
  (F1)  W = 2 atan2( r sin(2b - alpha), 1 - r cos(2b - alpha) )
  (F2)  W = 2 atan2( sin x, cos x + c )   with x = 2b - alpha, c = (1+r^2)/(2r) = 1/(2r cos alpha)
  (F3)  W = pi - 2alpha - 2 atan2( sin(2b-alpha), ... )   (endpoint form)
and the bound  W <= 2 asin r, plus inversion
  (I)   b_min(r,g) = pi/2 - alpha/2 + (1/2) atan(tan(g/2))  [= pi/2 - alpha/2 + g/4 for small g]
with the validity range 6pi + 8alpha - 32 asin(0.38) <= g <= pi - 2alpha.
"""
import math
import numpy as np

R0 = 0.38
G0 = 2 * math.pi - 16 * math.asin(R0)


def XD(r, b):
    s = math.sqrt(1 - r * r)
    c1 = np.array([s - 2 * r * math.sin(b) * math.cos(b), -2 * r * math.sin(b) ** 2])
    P1 = np.array([s, -r])
    return c1[0] * P1[1] - c1[1] * P1[0], float(c1 @ P1)


def W_of(r, b):
    X, D = XD(r, b)
    return 2 * math.atan2(X, D)


def main():
    print("(1) identity  X = r sin(x),  D - 1 = -r cos(x),  x = 2b - alpha")
    worst = (0.0, 0.0)
    for r in np.linspace(0.02, 0.98, 33):
        al = math.acos(r)
        for b in np.linspace(al / 2 + 1e-9, al, 41):
            x = 2 * b - al
            X, D = XD(r, b)
            worst = (max(worst[0], abs(X - r * math.sin(x))), max(worst[1], abs((D - 1) + r * math.cos(x))))
    print("    max |X - r sin x| =", worst[0], "   max |D-1 + r cos x| =", worst[1])

    print("\n(2) candidate formulas vs W = 2 atan2(X,D)")
    e1 = e2 = 0.0
    for r in np.linspace(0.05, 0.95, 19):
        al = math.acos(r)
        for b in np.linspace(al / 2 + 1e-9, al, 201):
            x = 2 * b - al
            W = W_of(r, b)
            f1 = 2 * math.atan2(r * math.sin(x), 1 - r * math.cos(x))
            f2 = 2 * math.atan2(math.sin(x), math.cos(x) + (1 + r * r) / (2 * r))
            e1 = max(e1, abs(W - f1))
            e2 = max(e2, abs(W - f2))
    print("    max |W - (F1)| =", e1)
    print("    max |W - (F2)| =", e2)

    print("\n(3) W/2 = arcsin( r sin(x/2) / sqrt(1 - r^2 sin^2(x/2)) )")
    e3 = 0.0
    for r in np.linspace(0.05, 0.95, 19):
        al = math.acos(r)
        for b in np.linspace(al / 2 + 1e-9, al, 201):
            x = 2 * b - al
            h = math.asin(r * math.sin(x / 2) / math.sqrt(1 - r * r * math.sin(x / 2) ** 2))
            e3 = max(e3, abs(W_of(r, b) / 2 - h))
    print("    max |W/2 - arcsin(...)| =", e3)

    print("\n(4) bound W <= 2 asin r  (equality at b = alpha, x = pi - alpha)")
    print("    r      max_b W (deg)      2 asin r (deg)   slack;  argmax b (deg)   alpha (deg)")
    for r in (0.375, 0.38, 0.40, 0.45, 0.49):
        al = math.acos(r)
        bs = np.linspace(al / 2 + 1e-12, al, 200001)
        Ws = np.array([W_of(r, b) for b in bs])
        i = int(np.argmax(Ws))
        print(f"    {r:.3f}  {math.degrees(Ws[i]):14.6f}  {math.degrees(2*math.asin(r)):13.6f}"
              f"   {math.degrees(2*math.asin(r))-math.degrees(Ws[i]):7.4f}   {math.degrees(bs[i]):12.5f}"
              f"   {math.degrees(al):9.5f}")
    print("    exact value at b=alpha: pi - 2 alpha ; exact W at the interior maximum")
    print("      (b = alpha/2 + pi/4, x = pi/2): 2 atan2(r, 1) = 2 r/(1+sqrt(1+r^2)) via half-angle")

    print("\n(5) inversion: b_min(r,g) = pi/2 - alpha/2 + atan(tan(g/2))/2")
    print("    r      g(deg)    b_min formula(deg)   b_min by bisection(deg)   diff")
    for r in (0.375, 0.38, 0.40, 0.45, 0.49):
        al = math.acos(r)
        Wmax = math.pi - 2 * al
        for gd in (2.661077475115173, 10.0, 30.0):
            g = math.radians(gd)
            if g > Wmax:
                print(f"    {r:.3f}  {gd:8.4f}   g > Wmax = {math.degrees(Wmax):.4f} deg -> empty")
                continue
            bf = math.pi / 2 - al / 2 + math.atan(math.tan(g / 2)) / 2
            lo, hi = al / 2, al
            for _ in range(200):
                mid = (lo + hi) / 2
                if W_of(r, mid) < g:
                    lo = mid
                else:
                    hi = mid
            bb = (lo + hi) / 2
            print(f"    {r:.3f}  {gd:8.4f}   {math.degrees(bf):18.9f}   {math.degrees(bb):22.9f}"
                  f"   {math.degrees(bf-bb):+.2e}")

    print("\n(6) W <= pi/2 everywhere? and other regularities")
    for r in (0.375, 0.38, 0.49):
        al = math.acos(r)
        bs = np.linspace(al / 2 + 1e-12, al, 100001)
        Ws = np.array([W_of(r, b) for b in bs])
        print(f"    r={r}: W in [{math.degrees(Ws.min()):.5f},{math.degrees(Ws.max()):.5f}] deg,"
              f" <= pi/2: {Ws.max() <= math.pi/2 + 1e-12},"
              f" max at b={math.degrees(bs[int(np.argmax(Ws))]):.4f}, alpha/2+pi/4={math.degrees(al/2+math.pi/4):.4f}")

    print("\n(7) is g in range at r=0.38? (for the interval outer contraction)")
    u = math.tan(G0 / 2)
    print("    g = 2pi - 16 asin(0.38) =", G0, "rad =", math.degrees(G0), "deg")
    print("    tan(g/2) =", u)
    for r in (0.375, 0.38, 0.40):
        al = math.acos(r)
        lo = 2 * G0 - 1  # placeholder
        cond_lo = 6 * math.pi + 8 * al - 32 * math.asin(R0)
        print(f"    r={r}: range [6pi+8alpha-32asinR0, pi-2alpha] = "
              f"[{math.degrees(cond_lo):.4f}, {math.degrees(math.pi-2*al):.4f}] deg;"
              f" g in range: {cond_lo <= G0 <= math.pi - 2*al}")


if __name__ == "__main__":
    main()
