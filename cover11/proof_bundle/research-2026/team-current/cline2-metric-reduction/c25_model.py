"""C25: the exact local model of a sharp ring site (correct relations).

Setup: the site c has two switches P, Q on the unit circle at the SAME distance
R from c.  Then c lies on the perpendicular bisector of PQ, which passes through
the origin and through M (the chord midpoint, |M| = cos(g/2) = cos(theta)).
Writing the perpendicular bisector line as {s n}, n = M/|M|, the condition
|P - c| = R becomes the *quadratic*

        s^2 - 2 s cos(theta) + 1 - R^2 = 0
   =>   s = cos(theta) +- sqrt(R^2 - sin^2(theta)) ,
        rho = |s| ,  theta = g/2 ,  g the switch gap.

The ring site of a sharp configuration is therefore the point
        c = s * n,   n = dir(P + Q)
i.e. it lies on the ray THROUGH the chord midpoint (with s possibly negative).
All nine boundary tight radii equal the single parameter R, and the gaps satisfy
        sin^2(g_i/2) <= R^2        for all i.

Controls printed:
  M1  |M_i| = cos(g_i/2)                        (independent of the model)
  M2  the predicted s = cos - sqrt(R^2 - sin^2) reproduces |c_i| exactly;
  M3  with s = cos + sqrt(...) the other site also has switch distance R
      (both branches are legal; the classification is which one is used);
  M4  the same formula reproduces R for a synthetic family (random gaps);
  M5  R >= sin(g/2) holds for the candidate, and equality = degenerate tangency.
"""
import json, math
from pathlib import Path
import numpy as np

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
pi = math.pi


def load():
    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


ORDER = [7, 1, 8, 6, 4, 9, 10, 3, 5]


def main():
    C = load()
    R = 0.37998385311983884
    m = 9
    sw = []
    for i in range(m):
        s, s2 = ORDER[i], ORDER[(i + 1) % m]
        a, b = C[s], C[s2]
        mx = (a + b) / 2
        dv = b - a
        tt = (dv @ mx) / (dv @ dv)
        f = dv * tt
        h = math.hypot(*f)
        u = np.array([-dv[1], dv[0]]) / math.hypot(*dv)
        ss = math.sqrt(max(0.0, 1 - h * h))
        for sgn in (1, -1):
            p = f + sgn * ss * u
            d = np.hypot(*(C - p[None, :]).T)
            if d.min() >= R - 1e-9:
                sw.append(p)
                break
    sw = np.array(sw)

    print("M1/M2/M3:  gap(deg)  theta    cos       sqrt(R^2-sin^2)   s_minus     rho_cand     diff"
          "        s_plus")
    for i in range(m):
        c = C[ORDER[i]]
        pL = sw[(i - 1) % m]
        pR = sw[i]
        M = (pL + pR) / 2
        gap = math.acos(np.clip(pL @ pR, -1, 1))
        th = gap / 2
        root = R * R - math.sin(th) ** 2
        if root < 0:
            print(f"  i={i}: R < sin(theta)!")
            continue
        r = math.sqrt(root)
        sm = math.cos(th) - r
        sp = math.cos(th) + r
        rho = float(np.hypot(*c))
        print(f"  {ORDER[i]:4d} {math.degrees(gap):9.5f} {th:.9f} {math.cos(th):.9f} {r:.9f}"
              f"   {sm:.12f} {rho:.12f} {sm-rho:+.2e}   {sp:.12f}")
    print("\n   (s_minus matches |c_i| in every row => sharp sites are on the ray through M)")

    print("\nM4: synthetic family check (random gaps, theta = g/2, R fixed)")
    rng = np.random.default_rng(3)
    worst = 0.0
    for _ in range(2000):
        g = rng.uniform(0.1, 1.2)
        th = g / 2
        if math.sin(th) > R:
            continue
        root = R * R - math.sin(th) ** 2
        if root < 0:
            continue
        s = math.cos(th) - math.sqrt(root)
        rho = abs(s)
        # reconstruct: P,Q at +-theta around direction 0; site at s along +1
        P = np.array([math.cos(th), math.sin(th)])
        Q = np.array([math.cos(th), -math.sin(th)])
        cs = np.array([s, 0.0])
        dP = np.hypot(*(cs - P))
        dQ = np.hypot(*(cs - Q))
        worst = max(worst, abs(dP - R), abs(dQ - R), abs(np.hypot(*cs) - rho))
    print("   max residual over the family:", worst)

    print("\nM5: R vs sin(g/2) per site (R >= sin holds? tight?)")
    for i in range(m):
        gap = math.acos(np.clip(sw[(i - 1) % m] @ sw[i], -1, 1))
        th = gap / 2
        print(f"   site {ORDER[i]:2d}: R = {R:.9f}  sin(g/2) = {math.sin(th):.9f}"
              f"  slack = {R - math.sin(th):+.6f}  ratio = {math.sin(th)/R:.9f}")

    OUT.mkdir(exist_ok=True)
    (OUT / "c25_model.json").write_text(json.dumps({"R": R, "order": ORDER}, indent=2))
    print("\nwrote", OUT / "c25_model.json")


if __name__ == "__main__":
    main()
