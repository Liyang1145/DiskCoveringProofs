"""C35: CORRECTIONS after the lead's audit (2026-09-24).

(1) ANTIPODAL MEMBERSHIP, correct form.
    x* = -c_i/|c_i| lies in cell(i) iff |x* - c_i|^2 <= |x* - c_j|^2 for all j,
    which expands to
            2 x* . (c_j - c_i)  <=  |c_j|^2 - |c_i|^2 .
    My earlier criterion (x* - c_i).(c_j - c_i) <= 0 is NOT equivalent; both are
    reported so the difference is visible.

(2) SWITCH SATURATION IS A "<=" STATEMENT.
    Covering gives min_j |P - c_j| <= R at every boundary point P, hence at
    every switch.  It does NOT give equality and it does NOT give equality for
    all nine switches.  Here we print the exact distances |P_i - c| for the two
    sites defining each switch, and compare with the covering radius R(C).

(3) UNSATURATED MODEL.  With free switch radii and equal endpoint distances
    (the corrected equality constraint), the model is
        rho_i cos(g_i/2) = |M_i| = cos(g_i/2)  =>  the same quadratic
        rho_i^2 - 2 rho_i cos(g_i/2) + 1 = r_i^2 ,   r_i = |c_i - P| <= R ,
    i.e. the sharp model with R replaced by the (free) common switch radius r_i.
"""
import json, math
from pathlib import Path
import numpy as np
from scipy.spatial import Voronoi

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


def main():
    C = load()
    R = 0.37998385311983884
    n = len(C)

    print("(1) ANTIPODE MEMBERSHIP: correct vs earlier criterion")
    print("    site  |c_i|     max_j[correct lhs]  max_j[my wrong lhs]   in cell?")
    for i in range(n):
        ci = C[i]
        rho = float(np.hypot(*ci))
        xs = -ci / rho
        corr = max(2 * float(xs @ (C[j] - ci)) - (float(C[j] @ C[j]) - float(ci @ ci))
                   for j in range(n) if j != i)
        wrong = max(float((xs - ci) @ (C[j] - ci)) for j in range(n) if j != i)
        print(f"    {i:4d}  {rho:.9f}   {corr:+.9e}          {wrong:+.9e}        "
              f"{'YES' if corr <= 0 else 'no'}")

    print("\n(2) SWITCH DISTANCES OF THE CANDIDATE (equality is NOT assumed)")
    sw = []
    for i in range(9):
        s, s2 = ORDER[i], ORDER[(i + 1) % 9]
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
    vals = []
    print("    switch  sites     |P-c_a|         |P-c_b|         max       max-R")
    for i in range(9):
        s, s2 = ORDER[i], ORDER[(i + 1) % 9]
        p = sw[i]
        d1 = float(np.hypot(*(p - C[s])))
        d2 = float(np.hypot(*(p - C[s2])))
        vals += [d1, d2]
        print(f"    {i}       ({s},{s2})   {d1:.15f}  {d2:.15f}  {max(d1,d2):.15f}  {max(d1,d2)-R:+.3e}")
    print("    max over all 18 endpoint distances:", max(vals), " R =", R)
    print("    min over all 18 endpoint distances:", min(vals))
    print("    NOTE: covering gives only  min_j |P-c_j| <= R  at each switch,")
    print("          so 18 values <= R is what is guaranteed, not equality.")

    print("\n(3) UNSATURATED MODEL: rho from the quadrat