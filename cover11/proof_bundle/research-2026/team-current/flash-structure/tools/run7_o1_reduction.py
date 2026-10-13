"""Run 7 (v2): O1 sufficient conditions -- SANITY CHECK ONLY, NOT A CERTIFICATE.

Component-wise facts (exact, proved):
  |v-c_j|^2 = |v|^2 + rho_j^2 - 2|v|rho_j cos(delta_j),  delta_j = cyclic angle(arg v, phi_j) in [0,pi],
  rho_j >= 1-r, r <= 1/2.
  (i) delta_j >= pi/2  => |v-c_j| >= rho_j >= 1-r >= r                       [FREE case]
  (ii) delta_j <  pi/2 => |v-c_j| >= rho_j sin(delta_j)  (min over |v| at |v| = rho_j cos delta_j)

Sufficient conditions for O1 evaluated below (ALL-j; the earlier two-neighbour reduction is RETRACTED):
  EXACT   : min over j not in {k,k+1} with delta_j < pi/2 of (rho_j sin(delta_j) - r)
  COARSE A: rho_j sin(delta_min) - r for all j, delta_min := min_j delta_j
  COARSE B: [delta_min >= pi/2] or [(1-r) sin(delta_min) - r]

The printed numbers are float64 sanity readings on one record configuration and a small structured
grid of legal ledgers. They are NOT interval certificates and must not be used to certify anything;
the reduction itself is the two-line computation above.
"""
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vgeom as V  # noqa: E402

OUT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "out"))
os.makedirs(OUT, exist_ok=True)
rep = []
def P(*a):
    s = " ".join(str(x) for x in a)
    rep.append(s)
    print(s)


def margins(r, t, o):
    phi, cen, gamma = V.build_ring(r, t, o)
    n = len(t)
    tc = V.tips_cyclic(r, t, o)
    exact, coarseA, coarseB, direct, dmin_all = math.inf, math.inf, math.inf, math.inf, math.inf
    for k in range(n):
        v = tc[k]["v"]
        th = math.atan2(v[1], v[0])
        d = {}
        for j in range(n):
            if j in (k, (k + 1) % n):
                continue
            dd = abs((th - phi[j] + math.pi) % (2 * math.pi) - math.pi)
            d[j] = dd
            direct = min(direct, V.dist(v, cen[j]) - r)
        dmin = min(d.values())
        dmin_all = min(dmin_all, dmin)
        for j, dd in d.items():
            rj = V.rho(t[j], r)
            if dd < math.pi / 2:
                exact = min(exact, rj * math.sin(dd) - r)
            coarseA = min(coarseA, rj * math.sin(dmin) - r)
        if dmin < math.pi / 2:
            coarseB = min(coarseB, (1 - r) * math.sin(dmin) - r)
    return dict(exact=exact, coarseA=coarseA, coarseB=coarseB, direct=direct,
                dmin=math.degrees(dmin_all))


def main():
    js, cen = V.load_fammin(os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "..",
        "research-2026", "team-20260923", "analytic-11", "fammin_config.json"))
    r = float(js["R_struct"][:20])
    ring, hub = V.classify(cen, r)
    ang = {i: math.atan2(cen[i][1], cen[i][0]) % (2 * math.pi) for i in ring}
    order = sorted(ring, key=lambda i: ang[i])
    t = [V.t_from_center(math.hypot(*cen[i]), r) for i in order]
    o = V.ledger_from_arcs(r, [ang[i] for i in order], t)
    m = margins(r, t, o)
    P(f"[record r={r:.17f}] EXACT={m['exact']:+.6e}  COARSE-A={m['coarseA']:+.6e}  "
      f"COARSE-B={m['coarseB']:+.6e}  direct={m['direct']:+.6e}  min delta={m['dmin']:.3f} deg")

    rng_ = np.random.default_rng(11)
    worst = {k: (math.inf, None) for k in ("exact", "coarseA", "coarseB", "direct")}
    ntot = 0
    for r in (0.3660254, 0.3700, 0.3750, 0.37998385, 0.3800):
        amax = math.asin(r)
        Emax = max(0.0, 9 * amax - math.pi)
        for idelta in (0.0, 0.25, 0.5, 0.75, 1.0):
            for _ in range(6):
                delta = idelta * Emax
                w_ = rng_.exponential(size=9)
                t = list(amax - delta * w_ / w_.sum())
                dl = [abs(t[i] - t[(i + 1) % 9]) for i in range(9)]
                cap = [t[i] + t[(i + 1) % 9] for i in range(9)]
                for lam in (0.0, 0.3, 0.6, 0.9):
                    lo, hi = 0.0, 1e6
                    for _ in range(200):
                        mid = 0.5 * (lo + hi)
                        gg = [min(cap[i] - 1e-13, dl[i] + mid * (cap[i] - dl[i])) for i in range(9)]
                        if sum(gg) < 2 * math.pi:
                            lo = mid
                        else:
                            hi = mid
                    gg = [min(cap[i] - 1e-13, dl[i] + hi * (cap[i] - dl[i])) for i in range(9)]
                    if abs(sum(gg) - 2 * math.pi) > 1e-12:
                        continue
                    if not all(gg[(i - 1) % 9] + gg[i] > t[(i - 1) % 9] + t[(i + 1) % 9] + 1e-12
                               for i in range(9)):
                        continue
                    oo = [t[i] + t[(i + 1) % 9] - gg[i] for i in range(9)]
                    if min(oo) < -1e-15:
                        continue
                    ntot += 1
                    m = margins(r, t, oo)
                    for key in worst:
                        if m[key] < worst[key][0]:
                            worst[key] = (m[key], (r, list(t), list(oo), m["dmin"]))
    P(f"[grid] legal ledgers (structured, sanity only): {ntot}")
    for key in ("exact", "coarseA", "coarseB", "direct"):
        wv, ctx = worst[key]
        P(f"[grid] worst {key:8s} = {wv:+.6e}   at r={ctx[0]} min-delta={ctx[3]:.2f} deg")
    wv, ctx = worst["coarseB"]
    P(f"[grid] COARSE-B worst case t(deg)={[round(math.degrees(x),3) for x in ctx[1]]}")
    P(f"        o(deg)={[round(math.degrees(x),3) for x in ctx[2]]}")
    P("[status] SANITY CHECK ONLY: float64 readings, not interval certificates; the O1 conditions "
      "remain UNPROVED over the ledger domain.")

    with open(os.path.join(OUT, "run7_o1_reduction.txt"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(rep) + "\n")
    print("written", os.path.join(OUT, "run7_o1_reduction.txt"))


if __name__ == "__main__":
    main()
