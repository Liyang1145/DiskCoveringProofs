"""R12-1: reconstruct the flat sector-2 configuration and measure the allowed w1.

Data (lead's Round12 message):
    r in (0,1), s = sqrt(1-r^2)
    c2 = (s, 0),  P1 = (s, -r),  P2 = (s, r)
    c1 = c2 + 2 r sin(b1) * (-cos b1, -sin b1)
    P0 = previous switch on the unit circle, at angle w1 CLOCKWISE from P1
    |P0 - c1| <= r,  |c1| <= s,  |P1 - c1| = r  (P1 an endpoint of c1's arc)

Outputs per (r, b1):
  * |P1 - c1| (should be r for the setup to be consistent),
  * the maximal w1 with P0 still inside B(c1, r)  -> w_max,
  * the minimal w1 for which P0 is at distance exactly r from c1 (the other
    endpoint of the chord) if such a P0 exists clockwise -> w_chord,
  * where P1 sits relative to the covered arc (which endpoint).
"""
import math
import numpy as np

OUT = None


def c1_of(r, b1):
    s = math.sqrt(1 - r * r)
    c2 = np.array([s, 0.0])
    d = np.array([-math.cos(b1), -math.sin(b1)])
    return c1_of_impl(r, b1)


def c1_of_impl(r, b1):
    s = math.sqrt(1 - r * r)
    c2 = np.array([s, 0.0])
    d = np.array([-math.cos(b1), -math.sin(b1)])
    return c2 + 2 * r * math.sin(b1) * d


def scan(r, b1, n=2000000):
    s = math.sqrt(1 - r * r)
    c1 = c1_of_impl(r, b1)
    P1 = np.array([s, -r])
    d1 = float(np.hypot(*(P1 - c1)))
    # the covered arc = {x on unit circle : |x - c1| <= r}
    t = np.linspace(0, 2 * math.pi, n + 1)[:-1]
    X = np.stack([np.cos(t), np.sin(t)], 1)
    dist = np.hypot(X[:, 0] - c1[0], X[:, 1] - c1[1])
    inside = dist <= r + 1e-12
    if not inside.any():
        return None
    # angular position of P1
    th1 = math.atan2(P1[1], P1[0])
    # w1 = clockwise angle from P1 to x  =>  w = ((th1 - th) mod 2pi)
    w = (th1 - t) % (2 * math.pi)
    win = w[inside]
    wmin, wmax = float(win.min()), float(win.max())
    # is the arc contiguous and does it contain P1 (w=0)?
    return {"c1": c1.tolist(), "|P1-c1|": d1, "|c1|": float(np.hypot(*c1)),
            "wmin": wmin, "wmax": wmax, "contains P1": win.min() < 1e-9,
            "halfwidth": 2 * math.asin(min(1.0, r / 2))}


def main():
    print("r      b1(deg)  |P1-c1|     |c1|      s        w_min(deg)  w_max(deg)  width(deg)  2asin(r/2)(deg)  P1 in arc")
    for r in (0.3, 0.38):
        s = math.sqrt(1 - r * r)
        for b1d in (10, 20, 30, 40, 50, 60, 70, 80, 90):
            b1 = math.radians(b1d)
            res = scan(r, b1, n=400000)
            if res is None:
                print(f"{r:.2f}  {b1d:5.0f}   c1-disk misses the unit circle entirely")
                continue
            print(f"{r:.2f}  {b1d:5.0f}   {res['|P1-c1|']:.6f}   {res['|c1|']:.6f}   {s:.6f}"
                  f"   {math.degrees(res['wmin']):9.4f}  {math.degrees(res['wmax']):9.4f}"
                  f"  {math.degrees(res['wmax']-res['wmin']):9.4f}  {math.degrees(res['halfwidth']):9.4f}"
                  f"      {res['contains P1']}")


if __name__ == "__main__":
    main()
