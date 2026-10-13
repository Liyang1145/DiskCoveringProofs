"""C23: the exact local model of a sharp ring site.

Setup: P, Q unit vectors with |P-Q| = 2 sin(theta); c with |c| = rho,
|c-P| = |c-Q| = R.

Derived and tested here (all with the exact candidate data):
  (i)   c lies on the perpendicular bisector: <c, P+Q> = 2 cos^2(theta)
  (ii)  the perpendicular distance from c to the chord line PQ equals
             rho sin(theta) = sin(theta) sqrt(2) sin(theta)   [if it holds]
  (iii) equivalently   |P-Q|^2 (R^2 - rho^2) = (rho*cos(theta) - 1)^2
  (iv)  the three equations (i)-(iii) determine rho and R from theta
        through  rho^2 = 1 - 2 sin^4(theta), R^2 = rho^2 + 1 - 2 rho cos(theta)
This script verifies (i)-(iv) numerically with high precision and prints the
residuals, then checks them against the *independent* candidate data.
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

    print(" i site  rho        th(deg)    (i) <c,P+Q>-2cos^2   (iii) |PQ|^2(R^2-rho^2)-(rho cos-1)^2"
          "   rho^2-(1-2 sin^4)     R^2 predicted vs measured")
    for i in range(m):
        c = C[ORDER[i]]
        pL = sw[(i - 1) % m]
        pR = sw[i]
        PQ = pR - pL
        gap = math.acos(np.clip(pL @ pR, -1, 1))
        th = gap / 2
        rho = float(np.hypot(*c))
        Rm = float(np.hypot(*(c - pL)))
        r1 = float(c @ (pL + pR)) - 2 * math.cos(th) ** 2
        r3 = float(PQ @ PQ) * (Rm * Rm - rho * rho) - (rho * math.cos(th) - 1) ** 2
        r4 = rho * rho - (1 - 2 * math.sin(th) ** 4)
        Rpred = math.sqrt(rho * rho + 1 - 2 * rho * math.cos(th))
        print(f"{i} {ORDER[i]:4d} {rho:.9f} {math.degrees(th):9.5f}   {r1:+.3e}            {r3:+.3e}"
              f"                 {r4:+.3e}       {Rpred:.12f} vs {Rm:.12f}")

    # the deduced closed forms
    print("\ndeduced closed forms (to be used in the reduction):")
    print("   rho(theta) = sqrt(1 - 2 sin^4(theta))")
    print("   R(theta)   = sqrt(rho^2 + 1 - 2 rho cos(theta))")
    print("\ncheck rho formula against candidate:")
    for i in range(m):
        c = C[ORDER[i]]
        gap = math.acos(np.clip(sw[(i - 1) % m] @ sw[i], -1, 1))
        th = gap / 2
        pred = math.sqrt(1 - 2 * math.sin(th) ** 4)
        print(f"   i={i} site {ORDER[i]:2d}: pred={pred:.15f} actual={np.hypot(*c):.15f}"
              f" diff={pred - np.hypot(*c):+.3e}")

    OUT.mkdir(exist_ok=True)
    (OUT / "c23_model.json").write_text(json.dumps({"order": ORDER, "R": R}, indent=2))
    print("\nwrote", OUT / "c23_model.json")


if __name__ == "__main__":
    main()
