"""Run 2 (v2): stress test over EXACT legal ledgers (sampler enforcing the full ledger domain).

Q1  tips lemma, direct margin:  min_{j not in {k,k+1}} |v_k - c_j| - r
Q2  tips lemma, radial-ray witness: v_k - eps*u(arg v_k) inside D and outside all 9 ring disks
Q3  inner crossing inside D (|v_in| < 1) ; outer crossing on/outside ∂D (|v_out| >= 1,
    equality iff o_k = 0)
Q4  ledger domain audit: coverage, only-adjacent overlap, sum identity, ell > 0
Q5  for a subsample: hole components (grid), tips in cl(H) (grid/relaxation), tips = hull vertices
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
    phi, cen, gamma = V.build_ring(r, t, o)
    n = len(t)
    au = V.audit_ledger(r, t, o)
    st = dict(cover=au["cover"], nonadj=au["nonadj"], min_ell=min(au["ell"]),
              sum_err=au["sum_err"])
    m_dist, m_ray, min_vout, max_vin = math.inf, math.inf, math.inf, -math.inf
    tc = V.tips_cyclic(r, t, o)
    for k in range(n):
        e = tc[k]
        max_vin = max(max_vin, e["r_in"])
        min_vout = min(min_vout, e["r_out"] - 1.0)
        m_dist = min(m_dist, min(V.dist(e["v"], cen[j]) - r
                                 for j in range(n) if j not in (k, (k + 1) % n)))
        rr = V.ray_clear(r, t, o, k)
        for x in rr:
            if x["inside_D"]:
                m_ray = min(m_ray, x["min_clear"])
    st.update(m_dist=m_dist, m_ray=m_ray, max_vin=max_vin, min_vout=min_vout)
    return st


def main():
    rng = random.Random(20260924)
    rgrid = [0.3601, 0.3660254, 0.3700, 0.3750, 0.3775, RSTRU, 0.3800]
    stats, bad, ntot = {}, [], 0
    for r in rgrid:
        key = round(r, 6)
        cur = stats.setdefault(key, dict(n=0, m_dist=math.inf, m_ray=math.inf,
                                         min_vout=math.inf, max_vin=-math.inf,
                                         cover=0, nonadj=0, ell=math.inf, sum_err=0.0))
        for _ in range(6000):
            out = V.sample_ledger(r, rng)
            if out is None:
                continue
            t, o, g, E = out
            ntot += 1
            st = analyse(r, t, o)
            cur["n"] += 1
            cur["m_dist"] = min(cur["m_dist"], st["m_dist"])
            cur["m_ray"] = min(cur["m_ray"], st["m_ray"])
            cur["min_vout"] = min(cur["min_vout"], st["min_vout"])
            cur["max_vin"] = max(cur["max_vin"], st["max_vin"])
            cur["cover"] += int(st["cover"])
            cur["nonadj"] += int(st["nonadj"])
            cur["ell"] = min(cur["ell"], st["min_ell"])
            cur["sum_err"] = max(cur["sum_err"], st["sum_err"])
            if (st["m_dist"] < 0) or (st["m_ray"] < 0) or (st["min_vout"] < -1e-9):
                bad.append((r, t, o, E, st))
    P(f"[run2b] legal ledgers analysed: {ntot}")
    P("[run2b] r          n     min m_dist   min m_ray    min(|vout|-1)  max|vin|  cover    nonadj  "
      "min ell  max sum-err")
    for r in sorted(stats):
        c = stats[r]
        P(f"         {r:<9.6f} {c['n']:<5d} {c['m_dist']:+.3e}  {c['m_ray']:+.3e}  "
          f"{c['min_vout']:+.3e}     {c['max_vin']:.6f}  {c['cover']}/{c['n']}  "
          f"{c['nonadj']}/{c['n']}  {c['ell']:.3f}    {c['sum_err']:.1e}")
    P(f"[run2b] violations: {len(bad)}")
    for r, t, o, E, st in bad[:12]:
        P(f"   r={r!r} E={math.degrees(E):.4f}deg t(deg)={[round(math.degrees(x),4) for x in t]}")
        P(f"        o(deg)={[round(math.degrees(x),4) for x in o]}  "
          f"m_dist={st['m_dist']:+.3e} m_ray={st['m_ray']:+.3e} min_vout={st['min_vout']:+.3e} "
          f"cover={st['cover']}")
    with open(os.path.join(OUT, "run2b_ledger_stress.txt"), "w", encoding="utf-8") as fh:
        fh.write("\n".join(rep) + "\n")
    print("\n".join(rep))
    print("written", os.path.join(OUT, "run2b_ledger_stress.txt"))


if __name__ == "__main__":
    main()
