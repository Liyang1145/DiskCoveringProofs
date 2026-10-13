"""R12-2: exact relations for the flat sector-2 setup.

Setup: r in (0,1), s = sqrt(1-r^2); c2 = (s,0); P1 = (s,-r); P2 = (s,r);
       c1 = c2 + 2 r sin(b1) * (-cos b1, -sin b1).
Let u = wrap(theta_P1 - theta_P0) be the clockwise angle from P1 to the switch P0.

Exact relations to be established and checked here:
  (A) |P1 - c1| = r  (P1 lies on the boundary of the radius-r arc of c1)
  (B) for any P0 on the unit circle with clockwise angle u from P1:
        |P0 - c1| <= r   <=>   u <= 2 b1        (u, 2b1 in [0,pi])
      i.e. the covered arc has diameter exactly 2 b1, with endpoints P1 (at
      u = 0) and P0 (at u = 2b1); equivalently |P0 - P1| = 2 r sin b1.
  (C) |c1| <= s is automatic in that range; the degenerate c1 = 0 is impossible.
  (D) P1 is the u = 0 endpoint (the counter-clockwise end of the arc), so P0 is
      clockwise from P1 at u = 2 b1 exactly.
"""
import math
import numpy as np

def build(r, b1):
    s = math.sqrt(1 - r * r)
    c2 = np.array([s, 0.0])
    d = np.array([-math.cos(b1), -math.sin(b1)])
    c1 = c2 + 2 * r * math.sin(b1) * d
    P1 = np.array([s, -r])
    return c1, P1, c2


def main():
    print("(A) |P1-c1| - r")
    worst = 0.0
    for r in (0.1, 0.3, 0.38, 0.5, 0.8):
        for b1d in (1, 5, 10, 20, 30, 40, 60, 80):
            b1 = math.radians(b1d)
            c1, P1, c2 = build(r, b1)
            worst = max(worst, abs(float(np.hypot(*(P1 - c1))) - r))
    print("    max |  |P1-c1| - r  | over the scan:", worst)

    print("\n(B) covered arc: |P0-c1| <= r  <=>  u <= 2b1")
    print("    r     b1(deg)   2b1(deg)   analytic boundary u where |P0-c1|=r   max |deg|")
    worst2 = 0.0
    for r in (0.2, 0.3, 0.38, 0.5):
        for b1d in (5, 10, 20, 30, 40):
            b1 = math.radians(b1d)
            c1, P1, c2 = build(r, b1)
            th1 = math.atan2(P1[1], P1[0])
            # find u in [0,pi] with |P0(u)-c1| = r, P0 at angle th1-u
            def f(u):
                P0 = np.array([math.cos(th1 - u), math.sin(th1 - u)])
                return float(np.hypot(*(P0 - c1))) - r
            lo, hi = 1e-12, math.pi
            if f(lo) > 0 or f(hi) < 0:
                print(f"    r={r} b1={b1d}: no sign change (f(0)={f(lo):.3e}, f(pi)={f(hi):.3e})")
                continue
            for _ in range(200):
                mid = (lo + hi) / 2
                if f(mid) <= 0:
                    lo = mid
                else:
                    hi = mid
            u = (lo + hi) / 2
            worst2 = max(worst2, abs(math.degrees(u - 2 * b1)))
            print(f"    {r:.2f}  {b1d:5.0f}   {math.degrees(2*b1):8.4f}   {math.degrees(u):12.6f}"
                  f"                {math.degrees(u-2*b1):+.2e}")
    print("    worst |u - 2b1| (deg):", worst2)

    print("\n(C) |c1| <= s in the range, and c1 = 0 impossible")
    for r in (0.2, 0.3, 0.38, 0.5, 0.8):
        s = math.sqrt(1 - r * r)
        mx = 0.0
        mn = 1e9
        for b1d in np.linspace(0.5, 89.5, 500):
            b1 = math.radians(b1d)
            c1, P1, c2 = build(r, b1)
            nrm = float(np.hypot(*c1))
            mx = max(mx, nrm)
            mn = min(mn, nrm)
        print(f"    r={r:.2f}  s={s:.6f}  |c1| in [{mn:.6f},{mx:.6f}]  (<= s always: {mx <= s + 1e-12})")

    print("\n(D) endpoints: P1 at u=0 and P0 at u=2b1, both at distance exactly r")
    for r, b1d in ((0.3, 20), (0.38, 30), (0.5, 40)):
        b1 = math.radians(b1d)
        c1, P1, c2 = build(r, b1)
        th1 = math.atan2(P1[1], P1[0])
        P0 = np.array([math.cos(th1 - 2 * b1), math.sin(th1 - 2 * b1)])
        print(f"    r={r} b1={b1d}: |P1-c1|={np.hypot(*(P1-c1)):.12f}  |P0-c1|={np.hypot(*(P0-c1)):.12f}"
              f"  |P0-P1|={np.hypot(*(P0-P1)):.12f}  vs 2sin(b1)={2*math.sin(b1):.12f}"
              f"  vs 2r sin b1={2*r*math.sin(b1):.12f}")


if __name__ == "__main__":
    main()
