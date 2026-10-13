"""Calibration 1: frozen-dual value on the lead flat chart, exact re-derivation checks.

Targets:
  (a) seven-factor value with the ROUND-18 dual (middle_inward_fiber_exchange_history.json)
      must reproduce lead/seven_factor_actualr_probe.json  joint_numeric 1.9443739591569895
      at x = [1.0, 2.685796, 1.0, 2.682435, 1.0, 0.499822, 1.0]  (values rounded to 6 dp).
  (b) consistency of the general chart at the flat point: gen_args(flat data) must equal
      flat_args for all seven atom arguments, and the coordinate checks must be consistent.
  (c) independent coordinate check: |c1-c2| == D1, |c3-c2| == D2, angle(c1,c2,c3)@c2 == b1+b2,
      |P1|=|P2|=1, |c2-P1| = R*s1 ... ; |c2| <= sqrt(1-r^2) (inward) with equality at flat.
"""
import json, math, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import r20_lib as L

LEAD = L.LEAD

# ---------------- (a) round-18 dual reproduction -------------------------------------
hist = json.loads((LEAD / "middle_inward_fiber_exchange_history.json").read_text())
row = min(hist, key=lambda r: r["continuous_numeric"])
z18 = np.array(row["z"])
x18 = [1.0, 2.685796, 1.0, 2.682435, 1.0, 0.499822, 1.0]
d18 = L.flat_args(x18)
v18 = L.flat_value(d18) if d18 is not None else None
# same with z18 substituted
def seven(d, z):
    tot = 0.0
    for fi, xx in zip(L.SEVEN_FACES, d["faces"]):
        tot += L.value(fi, xx, z)
    for fi, xx in zip(L.SEVEN_SWITCH, d["switches"]):
        tot += L.value(fi, xx, z)
    for fi, xx in zip(L.SEVEN_SECTOR, d["sectors"]):
        tot += L.value(fi, xx, z)
    return tot

print("(a) round18 z seven-factor at recorded SLSQP point :", seven(d18, z18))
print("    recorded joint_numeric (same z, full-precision x):", 1.9443739591569895)

# ---------------- full-precision re-optimization with round-18 z ---------------------
# (cheap local polish from the recorded point, to show the 6-dp x is not the issue)
from scipy.optimize import minimize, NonlinearConstraint

def decode_flat(x):
    d = L.flat_args(x)
    return d

def neg_round18(x, z=z18):
    d = L.flat_args(x)
    if d is None:
        return 1e3
    return -seven(d, z)

def cons_round18(x):
    d = L.flat_args(x)
    if d is None:
        return np.array([-1.0])
    t = x[0]
    mg = []
    for (a, u, v) in d["sectors"]:
        m = L.sector_margin(a, u, v, t)
        if m is None:
            return np.array([-1.0])
        mg += m
    return np.array(mg + [1.0])

bnds = [(L.TAU, 1), (.0233, L.PI), (.19, 1), (.0233, L.PI), (.19, 1), (1e-5, 1 - 1e-5), (0, 1)]
lb = [b[0] for b in bnds]; ub = [b[1] for b in bnds]
x0 = np.clip(np.array(x18), lb, ub)
res = minimize(neg_round18, x0, method="SLSQP", bounds=bnds,
               constraints={"type": "ineq", "fun": cons_round18}, options={"maxiter": 800, "ftol": 1e-13})
print("(a2) polished value (round18 z):", -res.fun, " x=", list(np.round(res.x, 8)))

# ---------------- (b) flat vs general chart at the same point ------------------------
x_flat = list(res.x)
p = L.flat_to_gen(x_flat)
dg = L.gen_args(p)
df = L.flat_args(x_flat)
print("\n(b) general chart at flat point:",
      "value=", L.gen_value(dg), " flat value=", L.flat_value(df))
print("    atom arg diffs (faces/switches/sectors):")
for tag, kf, kg in [("faces", "faces", "faces"), ("switch", "switches", "switches"), ("sector", "sectors", "sectors")]:
    for a, b in zip(df[kf], dg[kg]):
        print("     ", tag, [float(np.round(x - y, 14)) for x, y in zip(a, b)])
print("    A:", df["A"], dg["A"], " H:", df["H"], dg["H"], " b:", df["b1"], dg["b1"])

# ---------------- (c) coordinate consistency -----------------------------------------
c = L.consistency(p)
print("\n(c) consistency at flat point:")
for k, v in c.items():
    print("     %-16s %.15f" % (k, v))
print("    expected D1=D2=2r sin b ; angle = b1+b2 ; s(r)=%.15f" % math.sqrt(1 - (L.R * p["t"]) ** 2))

# ---------------- (d) frozen dual magnitude ------------------------------------------
print("\n(d) frozen (round21) z seven-factor at same point:", L.flat_value(df))
print("    frozen numeric_total_unrounded (whole 29):", L.FR.get("numeric_total_unrounded"))
names, mgs = L.gen_margins(p, dg)
print("\n(e) margins at flat point (min):", min(mgs), " argmin:", names[int(np.argmin(mgs))])
for n, m in zip(names, mgs):
    if m < 5e-3:
        print("      tight:", n, "%.3e" % m)
