"""Test the lead's proposed missing premise: the inner-root norm cap.

Chain to test (per boundary owner i with owned arc J_i of angular length theta_i, site c_i,
covering radius r, s = sqrt(1-r^2), n_i = unit vector at the arc midpoint):
  (C1) |c_i| <= s                      [inner-root norm cap; premise]
  (C2) covering at radius r  =>  J_i subset B(c_i,r)  =>  theta_i <= 2 asin r  =>  cos(theta_i/2) >= s
  (C3) n_i . c_i <= |c_i|
  =>   c_i . n_i <= cos(theta_i/2)   <=>  c_i on the inner side of its own arc chord
  <=>  the ray anchor->c_i lies inside the anchor-polygon interior sector at both anchors of J_i
  <=>  nesting slacks >= 0 at both anchors  <=>  claimed cyclicity identity holds there.

Numerical questions:
  Q1 does the campaign candidate satisfy C1?  which chain inequalities are tight?
  Q2 over random site sets: does C1 imply nest >= 0 at every anchor (no violation)?
  Q3 is (c.n <= cos(theta/2)) equivalent to nest >= 0?
"""
import json, math, sys
from pathlib import Path
import numpy as np
from fractions import Fraction

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom_exact import anchor_records, anchors_exact
from cover_radius_exact import cover_radius_exact

U = 0.33173203427623414

def owner_chain(S, verbose=False, tag=""):
    """per boundary owner: |c|, s, theta, c.n, cos(theta/2) and both nesting slacks."""
    S = np.asarray(S, float)
    r = cover_radius_exact(S)[0]
    s = math.sqrt(max(0.0, 1 - r * r))
    recs, anch = anchor_records(S)
    rows = []
    for k, rec in enumerate(recs):
        A = rec["A"]
        for side, arcs, other in (("cw", rec["arc_cw"], anch[(k - 1) % len(anch)]["A"]),
                                  ("ccw", rec["arc_ccw"], anch[(k + 1) % len(anch)]["A"])):
            if len(arcs) != 1:
                continue
            owner = arcs[0]
            c = S[owner]
            A2 = other
            midang = math.atan2(A[1], A[0]) + 0.5 * ((math.atan2(A2[1], A2[0]) - math.atan2(A[1], A[0]) + math.pi) % (2 * math.pi) - math.pi)
            n = np.array([math.cos(midang), math.sin(midang)])
            th = 2 * math.asin(min(1.0, float(np.linalg.norm(A - A2)) / 2))
            cn = float(c @ n)
            rows.append(dict(k=k, side=side, owner=owner, cn=cn, cnorm=float(np.linalg.norm(c)),
                             s=s, coshalf=math.cos(th / 2), theta=th, r=r,
                             nest=rec["nest_cw"] if side == "cw" else rec["nest_ccw"],
                             resid=rec["resid"]))
    return rows, r, s, recs

if __name__ == "__main__":
    out = open(HERE / "chain-check.txt", "w")
    cand = np.array([[float(Fraction(x)) for x in p]
                     for p in json.loads((HERE.parent.parent / "lead" / "improved-upper-test.json")
                                         .read_text())["centers"]])
    rows, r, s, recs = owner_chain(cand)
    print(f"candidate: r_exact={r:.15f}  s=sqrt(1-r^2)={s:.15f}")
    print("per boundary owner (candidate):")
    worst_c1 = -9e9; worst_c3 = -9e9
    for row in rows:
        worst_c1 = max(worst_c1, row["cnorm"] - s)
        worst_c3 = max(worst_c3, row["cn"] - row["coshalf"])
        print(f"   k={row['k']:2d} {row['side']:3s} owner={row['owner']:2d} |c|={row['cnorm']:.12f} "
              f"(cap s, |c|-s={row['cnorm']-s:+.3e})  c.n={row['cn']:.12f} "
              f"cos(theta/2)={row['coshalf']:.12f} (c.n-cos={row['cn']-row['coshalf']:+.3e}) "
              f"theta={row['theta']:.9f} (2asin r={2*math.asin(r):.9f}) nest={row['nest']:+.3e}")
        out.write(str(row) + "\n")
    print(f"  max(|c|-s) over owners = {worst_c1:+.3e}   max(c.n-cos(theta/2)) = {worst_c3:+.3e}")
    print()
    # Q2/Q3: random site sets
    rng = np.random.default_rng(4242)
    stats = dict(cap_ok_nest_bad=[], cap_bad_nest_bad=0, cap_bad=0, cap_ok=0, eq_mismatch=0)
    for trial in range(3000):
        n = int(rng.integers(7, 15))
        rad = rng.uniform(0.2, 0.99, n)
        ang = rng.uniform(0, 2 * math.pi, n)
        S = np.stack([rad * np.cos(ang), rad * np.sin(ang)], 1)
        rows, r, s, recs = owner_chain(S)
        if not rows:
            continue
        cap_ok = max(x["cnorm"] for x in rows) <= s
        nestmin = min(x["nest"] for x in rows)
        viol = nestmin < -1e-9
        if cap_ok: stats["cap_ok"] += 1
        else: stats["cap_bad"] += 1
        if cap_ok and viol:
            stats["cap_ok_nest_bad"].append((trial, n, r, s, nestmin,
                                             max(x["cnorm"] for x in rows)))
        if (not cap_ok) and viol: stats["cap_bad_nest_bad"] += 1
        for x in rows:
            eq1 = x["cn"] <= x["coshalf"] + 1e-12
            eq2 = x["nest"] >= -1e-9
            if eq1 != eq2:
                stats["eq_mismatch"] += 1
    print(f"random site sets (n=7..14): cap_ok={stats['cap_ok']} cap_bad={stats['cap_bad']}")
    print(f"  cap_ok AND nesting violation: {len(stats['cap_ok_nest_bad'])}")
    for t in stats["cap_ok_nest_bad"][:10]:
        print("    trial", t[0], "n=", t[1], "r=", round(t[2], 6), "s=", round(t[3], 9),
              "min_nest=", f"{t[4]:+.3e}", "max|c|=", round(t[5], 9))
    print(f"  cap_bad AND nesting violation: {stats['cap_bad_nest_bad']}")
    print(f"  rows where (c.n<=cos(theta/2)) differs from (nest>=0): {stats['eq_mismatch']}")
    out.close()
