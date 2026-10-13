"""Run 2: stress test over legal ledgers.

Questions (all w.r.t. the ring only; hubs not needed):
 Q1 tips lemma: is every inner crossing v_k outside every other ring disk?
    tested two ways: (a) direct distance margin  min_{j!=k,k+1} |v_k-c_j| - r
                      (b) radial-ray witness: v_k - eps*u(arg v_k) inside D and outside all 9 disks
 Q2 outer crossing: |v_out| >= 1 always, with equality iff o_k = 0 ?
 Q3 tip inside D: |v_in| < 1 ?
 Q4 staircase/multiplicity/coverage/essentiality (independent audit)
 Q5 is the whole hole H covered by the union of the 9 "curvilinear" closed cells?  (grid check:
    every hole point outside conv(tips) is reported)
"""
import math
import os
import random
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

RSTRU = 0.379983853119838689722261606136093214308718956


def analyse(r, t, o):
    """returns dict of margins for one legal ledger."""
    phi, cen, gamma = V.build_ring(r, t, o)
    n = len(t)
    au = V.audit_ledger(r, t, o)
    res = dict(cover=au["cover"], nonadj=au["nonadj"], min_ell=min(au["ell"]))
    worst_m, worst_ray, worst_out, worst_in = math.inf, math.inf, math.inf, -math.inf
    for k in range(n):
        p_in, p_out, M, h, d = V.crossings(r, cen[k], cen[(k + 1) % n])
        a, b = V.dist(p_in, (0, 0)), V.dist(p_out, (0, 0))
        v, v_out, r_in, r_out = (p_in, p_out, a, b) if a < b else (p_out, p_in, b, a)
        worst_in = max(worst_in, r_in)
        worst_out = min(worst_out, r_out - 1.0)
        m = min(V.dist(v, cen[j]) - r for j in range(n) if j not in (k, (k + 1) % n))
        worst_m = min(worst_m, m)
        # radial-ray witness
        rv = math.hypot(*v)
        ux, uy = v[0] / rv, v[1] / rv
        for eps in (1e-4, 1e-6):
            q = (v[0] - eps * ux, v[1] - eps * uy)
            if math.hypot(*q) >= 1.0:
                continue
            cl = min(V.dist(q, cen[j]) - r for j in range(n))
            worst_ray = min(worst_ray, cl)
    res.update(m_dist=worst_m, m_ray=worst_ray, max_v_in=worst_in, min_v_out_m1=worst_out)
    return res


def main():
    rng = random.Random(20260924)
    rgrid = [0.3601, 0.3660254, 0.3700, 0.3750, 0.3775, RSTRU, 0.38]
    stats = {}
    bad = []
    N = 0
    for r in rgrid:
        amax = math.asin(r)
        # (i) random legal ledgers
        for _ in range(3000):
            out = V.random_ledger(r, rng)
            if out is None:
                continue
            t, o = out
            N += 1
            st = analyse(r, t, o)
            key = round(r, 6)
            cur = stats.setdefault(key, dict(n=0, m_dist=math.inf, m_ray=math.inf,
                                             min_v_out=math.inf, max_v_in=-math.inf,
                                             cover=0, nonadj=0))
            cur["n"] += 1
            cur["m_dist"] = min(cur["m_dist"], st["m_dist"])
            cur["m_ray"] = min(cur["m_ray"], st["m_ray"])
            cur["min_v_out"] = min(cur["min_v_out"], st["min_v_out_m1"])
            cur["max_v_in"] = max(cur["max_v_in"], st["max_v_in"])
            cur["cover"] += int(bool(st["cover"]))
            cur["nonadj"] += int(bool(st["nonadj"]))
            if st["m_ray"] < 0 or st["m_dist"] < 0 or st["min_v_out_m1"] < -1e-12:
                bad.append((r, t, o, st))
        # (ii) structured families: 8 caps + 1 small, clumped arcs, etc.
        for j in range(9):
            for frac in (0.02, 0.1, 0.3, 0.6, 0.95):
                t = [amax * 0.999999] * 9
                t[j] = max(1e-6, (math.pi - 8 * amax * 0.999999) + 1e-6)
                if t[j] > amax or sum(t) < math.pi - 1e-12:
                    continue
                # distribute excess 0 and max (excess = sum t - pi)
                for excess_frac in (0.0, 0.5, 1.0):
                    t2 = list(t)
                    room = 9 * amax - sum(t2)
                    if room < -1e-12:
                        continue
                    t2 = [x + room * excess_frac / 9 for x in t2]
                    so = 2 * sum(t2) - 2 * math.pi
                    for layout in ("equal", "clumped"):
                        if layout == "equal":
                            o = [so / 9] * 9
                        else:
                            o = [0.0] * 9
                            o[j] = so
                        # enforce ell>0 by scaling down
                        for _ in range(300):
                            if min(2 * t2[i] - o[(i - 1) % 9] - o[i] for i in range(9)) > 1e-12:
                                break
                            o = [x * 0.97 for x in o]
                        else:
                            continue
                        if sum(o) < 1e-13:
                            continue
                        N += 1
                        st = analyse(r, t2, o)
                        key = round(r, 6)
                        cur = stats.setdefault(key, dict(n=0, m_dist=math.inf, m_ray=math.inf,
                                                         min_v_out=math.inf, max_v_in=-math.inf,
                                                         cover=0, nonadj=0))
                        cur["n"] += 1
                        cur["m_dist"] = min(cur["m_dist"], st["m_dist"])
                        cur["m_ray"] = min(cur["m_ray"], st["m_ray"])
                        cur["min_v_out"] = min(cur["min_v_out"], st["min_v_out_m1"])
                        cur["max_v_in"] = max(cur["max_v_in"], st["max_v_in"])
                        cur["cover"] += int(bool(st["cover"]))
                        cur["nonadj"] += int(bool(st["nonadj"]))
                        if st["m_ray"] < 0 or st["m_dist"] < 0 or st["min_v_out_m1"] < -1e-12:
                            bad.append((r, t2, o, st))
    P(f"[run2] legal ledgers analysed: {N}")
    P("[run2] r        n     min m_dist   min m_ray   min(|v_out|-1)  max|v_in|  cover  nonadj")
    for r in sorted(stats):
        c = stats[r]
        P(f"        {r:<8.6f} {c['n']:<5d} {c['m_dist']:+.3e}  {c['m_ray']:+.3e}  "
          f"{c['min_v_out']:+.3e}      {c['max_v_in']:.6f}  {c['cover']}/{c['n']}  {c['nonadj']}/{c['n']}")
    P(f"[run2] violations (m_dist<0 or m_ray<0 or |v_out|<1): {len(bad)}")
    for r, t, o, st in bad[:10]:
        P(f"   r={r!r} t(deg)={[round(math.degrees(x),4) for x in t]} "
          f"o(deg)={[round(math.degrees(x),4) for x in o]} st={ {k: round(v,6) if isinstance(v,float) else v for k,v in st.items()} }")
    with open(os.path.join(OUT, "run2_ledger_stress.txt"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(rep) + "\n")
    print("\n".join(rep[-8:]))
    print("written", os.path.join(OUT, "run2_ledger_stress.txt"))


if __name__ == "__main__":
    main()
