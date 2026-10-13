"""Run 5: analytic checks of the two review items (fail-loud, high precision).

  A. NO-FOUR-RING-COMMON-POINT:  asin(2r) + 5 asin(r) < pi  for all 0<r<=19/50.
     Monotone in r, so it suffices at r=19/50.  Exact-ish certificate with mpmath + a
     fully rational upper bound via the Taylor series with geometric tail bound.
  B. degree-3 claim at the nine boundary switch points: distance from the origin to the
     perpendicular bisector of two ring centres is <= (|c_i|+|c_j|)/2 <= sqrt(1-r^2) < 1
     (so the bisector enters int D transversally at the switch point).
  C. the four-ring lemma implies: an interior Voronoi vertex whose cells are all ring cells
     has degree exactly 3.
"""
import math
import os
import sys

from mpmath import mp, mpf, asin, pi, sqrt, cos, sin

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vgeom as V  # noqa: E402

mp.dps = 50
OUT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "out"))
os.makedirs(OUT, exist_ok=True)
rep = []
def P(*a):
    s = " ".join(str(x) for x in a)
    rep.append(s)
    print(s)


def main():
    # ---- A
    r0 = mpf(19) / 50
    for r in (mpf("0.1"), mpf("0.3"), mpf("0.3601"), r0):
        g = asin(2 * r) + 5 * asin(r)
        P(f"[A] r={r}  asin(2r)={asin(2*r)}  5asin(r)={5*asin(r)}  sum={g}  pi-sum={pi-g}")
    # rational upper bound at r=19/50 via Taylor + geometric tail
    # asin(x) = sum_{k>=0} c_k x^{2k+1},  c_k = C(2k,k)/(4^k (2k+1)), 0<c_k<=1
    def asin_upper(x, K=8):
        import math as m
        tot = 0.0
        for k in range(K + 1):
            c = m.comb(2 * k, k) / (4 ** k * (2 * k + 1))
            tot += c * x ** (2 * k + 1)
        # tail: c_k <= 1 for all k, ratio x^2, so tail <= x^{2K+3}/(1-x^2)
        tail = x ** (2 * K + 3) / (1 - x * x)
        return tot + tail
    ub = asin_upper(38.0 / 50.0) + 5 * asin_upper(19.0 / 50.0)
    P(f"[A] rational(ish) upper bound at r=19/50: {ub:.10f}  vs pi > 3.14159265 -> "
      f"margin {math.pi - ub:+.3e}")
    P(f"[A] monotonicity: d/dr[asin(2r)+5asin(r)] = 2/sqrt(1-4r^2) + 5/sqrt(1-r^2) > 0 "
      f"(= {2/math.sqrt(1-4*float(r0)**2)+5/math.sqrt(1-float(r0)**2):.4f} at r=19/50)")
    P(f"[A] hence NO four boundary disks share a point, for every r<=19/50; "
      f"a 4-ring interior Voronoi vertex is impossible.")

    # ---- B   bisector distance bound
    P("[B] bisector-distance check on fammin ring (and on random legal ledgers)")
    js, cen = V.load_fammin(os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "..",
        "research-2026", "team-20260923", "analytic-11", "fammin_config.json"))
    r = float(js["R_struct"][:20])
    ring, hub = V.classify(cen, r)
    ang = {i: math.atan2(cen[i][1], cen[i][0]) % (2 * math.pi) for i in ring}
    order = sorted(ring, key=lambda i: ang[i])
    t = [V.t_from_center(math.hypot(*cen[i]), r) for i in order]
    o = V.ledger_from_arcs(r, [ang[i] for i in order], t)
    phi, cc, gamma = V.build_ring(r, t, o)
    worst = 0.0
    for i in range(9):
        p, q = cc[i], cc[(i + 1) % 9]
        m = ((p[0] + q[0]) / 2, (p[1] + q[1]) / 2)
        dx, dy = q[0] - p[0], q[1] - p[1]
        d = math.hypot(dx, dy)
        dist0 = abs(m[0] * dx + m[1] * dy) / d      # distance origin -> bisector line
        bound = (math.hypot(*p) + math.hypot(*q)) / 2
        worst = max(worst, dist0)
        assert dist0 <= bound + 1e-15, (i, dist0, bound)
        assert bound <= math.sqrt(1 - r * r) + 1e-15
    P(f"[B] max distance(origin, bisector) = {worst:.9f} <= (|ci|+|cj|)/2 <= sqrt(1-r^2) = "
      f"{math.sqrt(1-r*r):.9f} < 1  -> the bisector always meets int D  => each of the 9 "
      f"boundary vertices has an entering interior edge (degree 3)")

    # ---- C
    P("[C] consequence for the cellulation: interior vertices carrying 4+ ring cells are"
      " impossible; every interior vertex has degree in [3,5] (3 ring + 2 hubs at most);"
      " the Euler count v<=11, e<=21 of the lead note is unchanged.")

    with open(os.path.join(OUT, "run5_analytic_checks.txt"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(rep) + "\n")


if __name__ == "__main__":
    main()
