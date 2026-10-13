"""C41: the lead's unsaturated reconstruction, implemented literally and verified.

PARAMETERS (per lead's exact message): 9 widths + 9 radii + 4 hub coordinates.
    P_prev = k n - (d/2) e ,   P = k n + (d/2) e ,
    k = cos(w/2) ,  d = 2 sin(w/2) ,
    a = rho_prev  (distance from the site to P_prev)
    b = rho_i     (distance from the site to P)
    x = (a^2 - b^2) / (2 d)
    h = sqrt( b^2 - (x - d/2)^2 ) = sqrt( a^2 - (x + d/2)^2 )
    c = (k - h) n + x e

Identifications verified below:
    |c - P| = b ,  |c - P_prev| = a ,  |c|^2 = (k-h)^2 + x^2 .
Feasibility: the radical >= 0, |c| < 1, and the branch k - h > 0 (inward).

My earlier radical sqrt(k^2-1-x^2+b^2) differs from (k-h) by exactly h(d/2 - b)/1 ...
we verify numerically that it is NOT equal, and that the lead's form is the correct one.
"""
import json, math
from pathlib import Path
import numpy as np

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
pi = math.pi
ORDER = [7, 1, 8, 6, 4, 9, 10, 3, 5]


def load():
    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


def switches_cyclic(C, R):
    out = []
    for i in range(9):
        s, s2 = ORDER[i], ORDER[(i + 1) % 9]
        a, b = C[s], C[s2]
        mx = (a + b) / 2
        dv = b - a
        tt = (dv @ mx) / (dv @ dv)
        f = dv * tt
        hh = math.hypot(*f)
        u = np.array([-dv[1], dv[0]]) / math.hypot(*dv)
        ss = math.sqrt(max(0.0, 1 - hh * hh))
        for sgn in (1, -1):
            p = f + sgn * ss * u
            d = np.hypot(*(C - p[None, :]).T)
            if d.min() >= R - 1e-9:
                out.append(p)
                break
    return np.array(out)


def main():
    C = load()
    R = 0.37998385311983884
    sw = switches_cyclic(C, R)          # sw[i] between ORDER[i] and ORDER[i+1]
    # site i is between sw[i-1] and sw[i];  w_i = angle(sw[i-1], sw[i])
    print("candidate data, lead's conventions  (a = rho_prev, b = rho_i)")
    print("  i site   w_i(deg)     k          d         a          b        x         h        xi=k-h"
          "   |c| actual   err")
    errs = []
    for i in range(9):
        pPrev = sw[(i - 1) % 9]
        p = sw[i]
        c = C[ORDER[i]]
        w = math.acos(np.clip(pPrev @ p, -1, 1))
        d = 2 * math.sin(w / 2)
        k = math.cos(w / 2)
        nv = pPrev + p
        n = nv / np.hypot(*nv)
        e = np.array([-n[1], n[0]])
        a = float(np.hypot(*(c - pPrev)))
        b = float(np.hypot(*(c - p)))
        x = (a * a - b * b) / (2 * d)
        h2 = b * b - (x - d / 2) ** 2
        h2b = a * a - (x + d / 2) ** 2
        h = math.sqrt(max(h2, 0.0))
        xi = k - h
        cand = xi * n + x * e
        err = float(np.hypot(*(cand - c)))
        errs.append(err)
        # my earlier (wrong) radical for comparison
        disc = k * k - 1 - x * x + b * b
        xi_old = k - math.sqrt(max(disc, 0.0))
        print(f"  {i} {ORDER[i]:4d} {math.degrees(w):9.5f} {k:.9f} {d:.9f} {a:.9f} {b:.9f}"
              f" {x:+.9f} {h:.9f} {xi:.9f}  {np.hypot(*c):.9f}  {err:.2e}")
        if i == 0:
            print(f"      equality of the two radical forms: h^2={h2:.12f}  a^2-(x+d/2)^2={h2b:.12f}")
            print(f"      my earlier radical branch would have given xi = {xi_old:.9f} (WRONG)")
    print("\nmax reconstruction error over the nine sites:", max(errs))

    print("\nidentifications (per lead):")
    worst = 0.0
    for i in range(9):
        pPrev = sw[(i - 1) % 9]
        p = sw[i]
        w = math.acos(np.clip(pPrev @ p, -1, 1))
        d = 2 * math.sin(w / 2)
        k = math.cos(w / 2)
        nv = pPrev + p
        n = nv / np.hypot(*nv)
        e = np.array([-n[1], n[0]])
        a = float(np.hypot(*(C[ORDER[i]] - pPrev)))
        b = float(np.hypot(*(C[ORDER[i]] - p)))
        x = (a * a - b * b) / (2 * d)
        h = math.sqrt(max(b * b - (x - d / 2) ** 2, 0.0))
        cand = (k - h) * n + x * e
        worst = max(worst, abs(float(np.hypot(*(cand - p))) - b),
                    abs(float(np.hypot(*(cand - pPrev))) - a))
    print("   max |  |c-p|-b  | and |  |c-pPrev|-a  |  =", worst)
    print("   radii are 9 (a_i = rho_(i-1), b_i = rho_i), not 18: the site's two")
    print("   switch distances are the SAME object viewed from the two switches.")

    print("\nfeasibility domain: radical b^2 - (x-d/2)^2 >= 0, i.e. |x - d/2| <= b")
    for i in range(9):
        pPrev = sw[(i - 1) % 9]
        p = sw[i]
        w = math.acos(np.clip(pPrev @ p, -1, 1))
        d = 2 * math.sin(w / 2)
        a = float(np.hypot(*(C[ORDER[i]] - pPrev)))
        b = float(np.hypot(*(C[ORDER[i]] - p)))
        x = (a * a - b * b) / (2 * d)
        slack = b * b - (x - d / 2) ** 2
        print(f"   i={i}: x-d/2 = {x - d/2:+.9f}  b = {b:.9f}  bipartity slack = {slack:+.9e}")

    OUT.mkdir(exist_ok=True)
    (OUT / "c41_recon.json").write_text(json.dumps({"max_err": max(errs)}, indent=2))
    print("\nwrote", OUT / "c41_recon.json")


if __name__ == "__main__":
    main()
