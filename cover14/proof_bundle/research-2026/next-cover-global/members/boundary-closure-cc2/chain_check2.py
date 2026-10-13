"""Targeted test of the lead's §1 chain on configurations that DO satisfy the inner-norm cap.
Sample site sets with a prescribed max norm m, keep only covers whose covering radius r obeys
m <= sqrt(1-r^2) (the cap), then check  (c.n <= cos(theta/2))  and  nest >= 0  at every anchor."""
import json, math, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom_exact import anchor_records
from cover_radius_exact import cover_radius_exact

rng = np.random.default_rng(777)

def owner_rows(S):
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
            c = S[arcs[0]]
            a1 = math.atan2(A[1], A[0]); a2 = math.atan2(other[1], other[0])
            d = (a2 - a1 + math.pi) % (2 * math.pi) - math.pi
            mid = a1 + 0.5 * d
            n = np.array([math.cos(mid), math.sin(mid)])
            th = abs(d)
            rows.append(dict(cn=float(c @ n), cnorm=float(np.linalg.norm(c)), s=s,
                             coshalf=math.cos(th / 2), theta=th,
                             nest=rec["nest_cw"] if side == "cw" else rec["nest_ccw"],
                             resid=rec["resid"], owner=int(arcs[0]), k=k, side=side))
    return rows, r, s

if __name__ == "__main__":
    res = {}
    for m in (0.75, 0.85, 0.92, 0.943):
        n_cap = n_ok = n_viol = 0
        worst_c = -9e9; worst_nest = 9e9; mismatch = []
        tried = 0
        while n_cap < 60 and tried < 20000:
            tried += 1
            n = int(rng.integers(9, 16))
            rad = rng.uniform(0.4 * m, m, n)
            ang = rng.uniform(0, 2 * math.pi, n)
            S = np.stack([rad * np.cos(ang), rad * np.sin(ang)], 1)
            rows, r, s = owner_rows(S)
            if not rows:
                continue
            if max(x["cnorm"] for x in rows) > s + 1e-15:
                continue
            n_cap += 1
            mn = min(x["nest"] for x in rows)
            if mn < -1e-9:
                n_viol += 1
            else:
                n_ok += 1
            worst_c = max(worst_c, max(x["cn"] - x["coshalf"] for x in rows))
            worst_nest = min(worst_nest, mn)
            for x in rows:
                if (x["cn"] <= x["coshalf"] + 1e-12) != (x["nest"] >= -1e-9):
                    mismatch.append(x)
        print(f"max|c|=m={m}: cap-satisfying configs kept={n_cap} (tried {tried})"
              f"  nesting-clean={n_ok}  violating={n_viol}")
        print(f"    max over rows of (c.n - cos(theta/2)) = {worst_c:+.3e}   min nest = {worst_nest:+.3e}"
              f"   rows where the two predicates differ = {len(mismatch)}")
        for x in mismatch[:4]:
            print("      ", {kk: (round(vv, 12) if isinstance(vv, float) else vv)
                             for kk, vv in x.items()})
        res[m] = dict(cap=n_cap, viol=n_viol, worst_cn_minus_cos=worst_c, min_nest=worst_nest)
    (HERE / "chain-cap-test.json").write_text(json.dumps(res, indent=1))
