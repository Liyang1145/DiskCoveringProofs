"""Run 3: pairwise crossing geometry scan (3 parameters: t_k, t_k1, gamma) at fixed r.

The ledger constraints restrict one adjacent pair only by
     |t_k - t_{k+1}| < gamma <= t_k + t_{k+1},      0 < t_i <= asin r.
Claims under test:
  P1  the INNER crossing (smaller radius) satisfies |v_in| < 1.
  P2  the OUTER crossing satisfies |v_out| >= 1, with equality iff gamma = t_k + t_{k+1} (o=0).
"""
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vgeom as V  # noqa: E402

OUT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "out"))
os.makedirs(OUT, exist_ok=True)
rep = []
def P(*a):
    s = " ".join(str(x) for x in a)
    rep.append(s)
    print(s)


def crossing_radii(r, tk, tk1, gamma):
    rk, rk1 = V.rho(tk, r), V.rho(tk1, r)
    d2 = rk * rk + rk1 * rk1 - 2 * rk * rk1 * math.cos(gamma)
    d = math.sqrt(max(0.0, d2))
    if d <= 0:
        return None
    h = math.sqrt(max(0.0, r * r - d * d / 4.0))
    Mx = (rk * math.cos(0.0) + rk1 * math.cos(gamma)) / 2
    My = (rk1 * math.sin(gamma)) / 2
    nx, ny = math.sin(gamma) * rk1 / d, (rk - rk1 * math.cos(gamma)) / d
    p1 = (Mx - h * nx, My - h * ny)
    p2 = (Mx + h * nx, My + h * ny)
    return math.hypot(*p1), math.hypot(*p2)


def main():
    for r in (0.3601, 0.3660254, 0.3700, 0.3750, 0.37998385, 0.3800):
        amax = math.asin(r)
        worst_in = (-math.inf, None)     # max of |v_in|
        worst_out = (math.inf, None)     # min of |v_out| - 1
        worst_out_pos = (math.inf, None) # min over gamma < t_k+t_{k+1} strictly
        N = 0
        NG = 220
        for it in range(NG + 1):
            tk = amax * it / NG
            for jt in range(NG + 1):
                tk1 = amax * jt / NG
                lo = abs(tk - tk1) + 1e-12
                hi = tk + tk1 - 1e-12
                if tk <= 0 or tk1 <= 0 or hi <= lo:
                    continue
                for ig in range(1, 121):
                    gamma = lo + (hi - lo) * ig / 121
                    rr = crossing_radii(r, tk, tk1, gamma)
                    if rr is None:
                        continue
                    a, b = rr
                    vin, vout = min(a, b), max(a, b)
                    N += 1
                    if vin > worst_in[0]:
                        worst_in = (vin, (math.degrees(tk), math.degrees(tk1),
                                          math.degrees(gamma)))
                    if vout - 1 < worst_out[0]:
                        worst_out = (vout - 1, (math.degrees(tk), math.degrees(tk1),
                                                math.degrees(gamma),
                                                math.degrees(tk + tk1 - gamma)))
                    if tk + tk1 - gamma > 1e-9 and vout - 1 < worst_out_pos[0]:
                        worst_out_pos = (vout - 1, (math.degrees(tk), math.degrees(tk1),
                                                    math.degrees(gamma),
                                                    math.degrees(tk + tk1 - gamma)))
        P(f"[r={r}] samples={N}")
        P(f"   P1 max|v_in| = {worst_in[0]:.9f}  at (t_k,t_k1,gamma)={tuple(round(x,4) for x in worst_in[1])}"
          f"   (claim < 1)")
        P(f"   P2 min(|v_out|-1) = {worst_out[0]:+.3e} at ...={tuple(round(x,4) for x in worst_out[1])}")
        P(f"   P2b min over o>0   = {worst_out_pos[0]:+.3e} at (t_k,t_k1,gamma,o)="
          f"{tuple(round(x,4) for x in worst_out_pos[1])}")
    with open(os.path.join(OUT, "run3_pair_scan.txt"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(rep) + "\n")


if __name__ == "__main__":
    main()
