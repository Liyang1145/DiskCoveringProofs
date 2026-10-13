"""
DECISIVE re-derivation: which side of x0 is feasible?

Raw geometry, no formula:
    theta_i(x,y) = atan2(y_i sin b_i, x - y_i cos b_i)
    feasible  <=>  0 < theta_i < pi - b_i  and  sum_i theta_i = pi.
For the natural inner optimum y_i = 1 we tabulate  S(x) = sum_i theta_i(x,1)
on a grid x in (0,1] for several beta, to READ OFF whether S = pi happens at
the small root (then x <= x0 is wrong and x in [x0,1] is feasible) or at x=1.
Also evaluates the true max over (x,y) via the corrected direct solver.
"""
import json
import sys
import numpy as np
sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2")
import envelope_clean as EC
import direct_full as DF

PI = EC.PI
cases = {
    'pi/4^3': [PI / 4] * 3,
    'pi/3^3': [PI / 3] * 3,
    '1.0^3': [1.0] * 3,
    '(pi/2)^3': [PI / 2] * 3,
    'lead_cand': [0.9223829833, 1.1925065472, 1.1925065472],
    '1.2^3': [1.2] * 3,
    '1.4,1.28,0.5': [1.4, 1.28, 0.5],
}
out = {}
for name, b in cases.items():
    b = np.asarray(b, float)
    Bsum = float(b.sum())
    xs = np.linspace(0.02, 1.0, 25)
    tab = []
    for x in xs:
        th = EC.theta(b, x)
        S = float(th.sum())
        tab.append((round(float(x), 4), round(S, 6),
                    bool(np.all(th < PI - b)), bool(np.all(th > 0))))
    # root of S(x) = pi by bisection (S strictly decreasing in x)
    def f(x):
        return EC.H(b, x) - PI
    xr = None
    feasibility = None
    if f(1.0) <= 0:
        # S(1) <= pi: the constraint is satisfied at the largest x, so x<=1 all
        # feasible; the crossing, if any in (0,1], is at x0 = the value where
        # S crosses pi from above (i.e. x slightly below 1 has S>pi).
        xr = 1.0 if abs(f(1.0)) < 1e-14 else None
        feasibility = 'x <= x0 with x0 = 1 (S(1)=pi exactly)'
    else:
        lo, hi = 1e-12, 1.0
        for _ in range(200):
            mid = 0.5 * (lo + hi)
            if f(mid) > 0:
                lo = mid
            else:
                hi = mid
        xr = 0.5 * (lo + hi)
        feasibility = 'x in (0, x0] (S(1)>pi)'
    A_x1_y1 = (float(np.sin(b).sum()) if f(1.0) <= 0 else None)
    v, xv, yv = DF.inner_max(b)
    out[name] = dict(beta=b.tolist(), Bsum=Bsum,
                     S_at_x1=float(EC.H(b, 1.0)),
                     S_at_0p02=float(EC.H(b, 0.02)),
                     root_S_eq_pi=xr,
                     feasibility=feasibility,
                     x0_theorem=float(EC.x0_theorem(b)),
                     A_x1_y1=A_x1_y1,
                     direct_max=v, direct_x=xv, direct_y=yv.tolist(),
                     table=tab[:8] + tab[-6:])
    print(name, json.dumps({k: v for k, v in out[name].items() if k != 'table'}), flush=True)

with open(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\feasibility_direction.json", 'w') as f:
    json.dump(out, f, indent=1)
print('DONE')
