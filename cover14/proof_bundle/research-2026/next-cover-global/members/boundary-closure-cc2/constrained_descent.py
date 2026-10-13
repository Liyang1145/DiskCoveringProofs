"""Constrained descent: minimise the EXACT covering radius while keeping the cyclicity
violation (nesting slack < 0) and the combinatorial type, from the saved violating configs.
Goal: a 14-disk cover of D with r <= U that violates the claimed cyclicity identity."""
import json, math, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom_exact import anchor_records
from cover_radius_exact import cover_radius_exact

U = 0.33173203427623414
CAND = np.array([[float(__import__("fractions").Fraction(x)) for x in p]
                 for p in json.loads((HERE.parent.parent / "lead" / "improved-upper-test.json")
                                     .read_text())["centers"]])

def state(S):
    r = cover_radius_exact(S)[0]
    recs, anch = anchor_records(S)
    if len(recs) == 0:
        return r, None, None, None
    mn = min(min(r_["nest_ccw"], r_["nest_cw"]) for r_ in recs)
    mx = max(abs(r_["resid"]) for r_ in recs)
    part = sorted([x for r_ in recs for x in r_["pair"]])
    return r, mn, mx, part

def descend(S0, max_pass=40):
    S = S0.copy()
    r0, mn0, mx0, part0 = state(S)
    best = (r0, S.copy(), mn0, mx0)
    h = 5e-3
    for it in range(max_pass):
        improved = False
        for i in range(len(S)):
            for ang in np.linspace(0, 2 * math.pi, 12, endpoint=False):
                T = S.copy()
                T[i] = S[i] + h * np.array([math.cos(ang), math.sin(ang)])
                if (T[i] ** 2).sum() > 0.999 ** 2:
                    continue
                rr, mn, mx, part = state(T)
                if mn is None or mn > -1e-9:
                    continue               # violation lost
                if part != part0:
                    continue               # combinatorial type changed
                if rr < best[0] - 1e-13:
                    best = (rr, T.copy(), mn, mx)
                    improved = True
        if not improved:
            h *= 0.5
            if h < 1e-9:
                break
        else:
            S = best[1].copy(); h = min(h * 1.5, 1e-2)
    return best

if __name__ == "__main__":
    cfgs = json.loads((HERE / "violating-configs.json").read_text())
    print(f"U = {U:.12f}   campaign candidate r = {cover_radius_exact(CAND)[0]:.12f}")
    rows = []
    for idx, cfg in enumerate(cfgs[:6]):
        S0 = np.array(cfg["sites"])
        r0, mn0, mx0, _ = state(S0)
        r1, S1, mn1, mx1 = descend(S0)
        status = "LEGAL (r<=U)" if r1 <= U else "still above U"
        print(f"cfg#{idx}: start r={r0:.9f} (nest={mn0:+.2e}) -> r={r1:.9f} r-U={r1-U:+.3e} "
              f"nest={mn1:+.3e} resid={mx1:.2e}  {status}")
        rows.append(dict(idx=idx, r=r1, U=U, min_nest=mn1, max_resid=mx1, sites=S1.tolist()))
    rows.sort(key=lambda d: d["r"])
    (HERE / "constrained-descent.json").write_text(json.dumps(rows, indent=1))
    print("best r =", f"{rows[0]['r']:.12f}", " r-U =", f"{rows[0]['r']-U:+.3e}",
          " min_nest =", rows[0]["min_nest"])
