"""C22: extract the exact closed form of the sharp 9-ring stratum from data.

For each ring site i (exact candidate coordinates) collect
    rho_i = |c_i|,  gap_i = angular distance between its two switches,
    R     = distance from c_i to each switch (all equal to 0.379983853119839)
and test candidate closed forms:
    (A) rho = 1/cos(g/2)                       (rho*cos(g/2) = 1)
    (B) rho = cos(g/2)                         (rho/sec(g/2) = cos^2)
    (C) R   = tan(g/2)                         (R = tan)
    (D) 1 = rho*cos(g/2) + R*sin(g/2)
    (E) R = rho*(1 - cos(g/2))
    (F) rho*sin(g/2) = something fixed
Also: are the nine gaps equal?  (No: 32.18 .. 44.49 deg.)
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
    rows = []
    print("site   |c|        gap(deg)   cos(g/2)   sin(g/2)   |c|cos   |c|sin   "
          "A:rho*cos  B:rho-cos  C:R-tan  D:1-(rhocos+Rsin)  E:R-rho(1-cos)")
    for i in range(m):
        c = C[ORDER[i]]
        pL = sw[(i - 1) % m]
        pR = sw[i]
        gap = math.acos(np.clip(pL @ pR, -1, 1))
        th = gap / 2
        rho = float(np.hypot(*c))
        A = rho * math.cos(th)
        B = rho - math.cos(th)
        Cv = R - math.tan(th)
        Dv = 1 - (rho * math.cos(th) + R * math.sin(th))
        Ev = R - rho * (1 - math.cos(th))
        print(f"{ORDER[i]:4d} {rho:.9f} {math.degrees(gap):9.5f} {math.cos(th):.9f} {math.sin(th):.9f}"
              f" {A:.9f} {rho*math.sin(th):.9f}  {A-1:+.3e}  {B:+.9f}  {Cv:+.3e}  {Dv:+.3e}  {Ev:+.3e}")
        rows.append({"site": ORDER[i], "rho": rho, "gap": gap, "A": A, "D": Dv, "E": Ev})
    OUT.mkdir(exist_ok=True)
    (OUT / "c22_fit.json").write_text(json.dumps(rows, indent=2))
    print("\nwrote", OUT / "c22_fit.json")


if __name__ == "__main__":
    main()
