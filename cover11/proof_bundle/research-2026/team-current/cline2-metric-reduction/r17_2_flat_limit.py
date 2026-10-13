"""R17-2: correct scaling test for the sector height near alpha2 = pi.

Physical chart (lead's flat patch): r in [3/8,19/50], s = sqrt(1-r^2), P1,P2 on the unit
circle with |P1 P2| = 2 sin(w2/2), and the middle site c2 at distance exactly r from BOTH
P1 and P2 (switch radii). Then alpha2 = angle at c2 between P1 and P2 and
h = dist(c2, span(P1,P2)).

Flat limit: as alpha2 -> pi the triangle (c2,P1,P2) degenerates, i.e. c2 approaches the
midpoint of the chord, and h -> 0. Here we track, for fixed P1,P2 (fixed width w2), the
position of c2 on the perpendicular bisector satisfying |c2 - P1| = |c2 - P2| = r, and
measure (eps, h) with eps = pi - alpha2.
"""
import math
import json


def main():
    print(" r        w2(deg)   rho=|c2P| target   h          eps=pi-alpha2    h/eps       chord/2")
    for rd in (0.375, 0.38, 0.37999):
        s = math.sqrt(1 - rd * rd)
        for w2d in (30.0, 60.0, 90.0, 120.0):
            w2 = math.radians(w2d)
            # chord endpoints symmetric about the x-axis at the unit-circle chord of width w2
            mid = math.cos(w2 / 2)
            half = math.sin(w2 / 2)
            P1 = (mid, -half)
            P2 = (mid, half)
            # c2 on the perpendicular bisector (the x-axis here) with |c2-P1| = r
            # |c2 - P1|^2 = (x-mid)^2 + half^2 = r^2  =>  x = mid - sqrt(r^2 - half^2)
            disc = rd * rd - half * half
            if disc < 0:
                print(f" {rd:.5f}  {w2d:8.2f}   impossible (half>r)")
                continue
            # two roots; the physical one is the inner root (site inside the disk)
            for tag, x in (("outer", mid + math.sqrt(disc)), ("inner", mid - math.sqrt(disc))):
                c2 = (x, 0.0)
                v1 = (P1[0] - x, P1[1])
                v2 = (P2[0] - x, P2[1])
                alpha = math.acos(max(-1.0, min(1.0, (v1[0] * v2[0] + v1[1] * v2[1])
                                                 / (math.hypot(*v1) * math.hypot(*v2)))))
                h = abs(x - mid)          # distance from c2 to the chord span(P1,P2)
                eps = math.pi - alpha
                if tag == "inner" and eps < 1e-3:
                    print(f" {rd:.5f}  {w2d:8.2f}   {rd:.9f}        {h:.6e}  {eps:.6e}   {h/eps:.6f}"
                          f"   {half:.6f}")
    print("\nnote: eps -> 0 exactly when the chord half-length equals r, i.e. w2 = 2 asin r;")
    print("the near-flat regime is therefore approached by w2 -> 2 asin r, not by moving c2.")
    print("\nTail of the family (w2 -> 2 asin r) with r fixed:")
    for rd in (0.38,):
        s = math.sqrt(1 - rd * rd)
        wstar = 2 * math.asin(rd)
        print(f"  r = {rd}:  w2* = 2 asin r = {math.degrees(wstar):.6f} deg")
        print("   %12s %14s %14s %12s" % ("w2* - w2", "h", "eps", "h/eps"))
        for d in (1e-2, 1e-3, 1e-4, 1e-5, 1e-6):
            w2 = wstar - d
            mid = math.cos(w2 / 2)
            half = math.sin(w2 / 2)
            disc = rd * rd - half * half
            if disc < 0:
                continue
            x = mid - math.sqrt(disc)
            P1 = (mid, -half)
            P2 = (mid, half)
            v1 = (P1[0] - x, P1[1])
            v2 = (P2[0] - x, P2[1])
            alpha = math.acos(max(-1.0, min(1.0, (v1[0] * v2[0] + v1[1] * v2[1])
                                             / (math.hypot(*v1) * math.hypot(*v2)))))
            h = abs(mid - x)
            eps = math.pi - alpha
            print("   %12.2e %14.6e %14.6e %12.6f" % (d, h, eps, h / eps if eps else float('nan')))


if __name__ == "__main__":
    main()
