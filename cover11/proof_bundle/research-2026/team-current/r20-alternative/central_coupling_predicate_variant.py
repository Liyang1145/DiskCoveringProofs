# -*- coding: utf-8 -*-
"""r20-alternative / predicate-variant control: same instance B, closed-exterior (>=) vs open-exterior (>)."""
from fractions import Fraction as F
from itertools import combinations

K = ((F(0), F(0)), F(5))
D = ((F(6), F(0)), F(5))


def d2(p, q):
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2


# the two rational circle-circle intersection points of bd K and bd D
pts = [(F(3), F(4)), (F(3), F(-4))]
print("instance B: K = B(0,5), D = B((6,0),5); intersections (3,+-4) lie on BOTH boundaries")
for p in pts:
    inK = d2(p, K[0]) <= K[1] ** 2          # closed inside  (<=) : on passes
    outD_strict = d2(p, D[0]) > D[1] ** 2   # open exterior  (>)  : on FAILS  -> Omega = K \ D
    outD_closed = d2(p, D[0]) >= D[1] ** 2  # closed exterior(>=) : on PASSES -> Omega = K \ int D
    print("   p=%-9s |p-qK|^2=%-4s (=25 on bd)  inK(<=)=%s ; outD(>)=%s ; outD(>=)=%s"
          % (p, d2(p, K[0]), inK, outD_strict, outD_closed))
print("=> with the STRICT (> r) exterior the two boundary points are EXCLUDED (Omega = K \\ D),")
print("   while the CENTRAL-constraint form needs the CLOSED (>= r) exterior: they ARE members (Omega = K \\ int D).")
print("   This is exactly the 'B \\ B' vs 'B \\ int B' distinction; both must be labelled in the note.")
