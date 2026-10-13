"""Deformation scan (evaluation only, NO optimizer starts).

Take the certified cover's own local patch data as base point:
   x* : t, alpha1,u1,s1=t, alpha2=2.96735404, s2=t, alpha3,v3, A, H
and move along the natural "flattening" directions:
   (i)   alpha2 up to pi with everything else fixed            -> does J increase/decrease?
   (ii)  s1,s2 down from t (non-tight switches) at fixed alpha2
   (iii) the joint corner push (alpha2 -> pi and s1,s2 -> t)
Legality (all margins of the general chart) is reported for each point.
Also compares with the flat slice value at the same outer data.
"""
import json, math, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import r20_lib as L

PI, R = L.PI, L.R
d0 = json.load(open(HERE / "cand_local_data.json"))
t = d0["t"]
base = dict(t=t, a1=d0["a1"], u1=d0["u1"], s1=t, a2=d0["a2"], s2=t, a3=d0["a3"], v3=d0["v3"],
            A=d0["A"], H=d0["H"])
THRESH = 28.10704541577262956809
FLATUB = 28.106948822740861261

print("base point (certified cover local data):")
g = L.gen_args(base)
print("  alpha2 = %.12f  (pi-alpha2 = %.6f)   s1=s2=t=%.12f" % (base["a2"], PI - base["a2"], t))
print("  J = %.12f   value - threshold = %+.6e" % (L.gen_value(g), L.gen_value(g) - THRESH))
print("  b1=%.9f b2=%.9f  A=%.9f B=%.9f" % (g["b1"], g["b2"], g["A"], g["B"]))

print("\n(i) alpha2 sweep, everything else fixed (s1=s2=t):")
print("   alpha2        pi-alpha2     b1        b2        B         J          margins(min)  legal")
rows = []
for a2 in np.linspace(0.05, PI, 41):
    p = dict(base, a2=float(a2))
    g = L.gen_args(p)
    if g is None:
        print("   %9.6f     %8.6f    -- infeasible (chart) --" % (a2, PI - a2))
        continue
    names, mg = L.gen_margins(p, g)
    J = L.gen_value(g)
    ok = min(mg) > -1e-9
    rows.append((a2, J, ok, min(mg)))
    print("   %9.6f     %8.6f   %7.5f  %7.5f  %7.5f  %10.6f   %+.2e    %s"
          % (a2, PI - a2, g["b1"], g["b2"], g["B"], J, min(mg), "yes" if ok else "NO"))
best = max([r for r in rows if r[2]], key=lambda r: r[1])
print("   max over sweep (legal): J = %.9f at alpha2 = %.6f" % (best[1], best[0]))

print("\n(ii) s1,s2 sweep at alpha2 = pi - 0.17423861 (candidate value):")
for ds in [0.0, 0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2]:
    p = dict(base, s1=t - ds, s2=t - ds)
    g = L.gen_args(p)
    if g is None:
        print("   s=t-%5.3f  infeasible" % ds)
        continue
    names, mg = L.gen_margins(p, g)
    print("   s=t-%5.3f  J=%10.6f  minmargin=%+.2e  (legal %s)" % (ds, L.gen_value(g), min(mg), min(mg) > -1e-9))

print("\n(iii) joint corner push (alpha2 -> pi, s -> t):")
for k in [0.0, 0.25, 0.5, 0.75, 1.0]:
    a2 = base["a2"] + k * (PI - base["a2"])
    s = t - (1 - k) * (t - t)
    p = dict(base, a2=a2, s1=s, s2=s)
    g = L.gen_args(p)
    if g is None:
        print("   k=%.2f infeasible" % k)
        continue
    names, mg = L.gen_margins(p, g)
    print("   k=%.2f  alpha2=%.6f  s=%.6f  J=%10.6f  minmargin=%+.2e" % (k, a2, s, L.gen_value(g), min(mg)))

print("\n(iv) flat slice at the same outer data (alpha2=pi, s1=s2=t, same A,H):")
pf = dict(base, a2=PI)
gf = L.gen_args(pf)
if gf is None:
    print("   infeasible with the same A,H")
else:
    print("   J_flat_sameAH = %.12f   margins min %+.2e" % (L.gen_value(gf), min(L.gen_margins(pf, gf)[1])))
# optimise H only (1-D golden search, NOT counted as an optimization start: 1-D line search)
def J_of_H(H):
    p = dict(base, a2=PI, H=H)
    g = L.gen_args(p)
    if g is None:
        return -1e9
    mg = L.gen_margins(p, g)[1]
    if min(mg) < -1e-9:
        return -1e9
    return L.gen_value(g)
lo, hi = 0.02, 2 * R
for _ in range(200):
    m1 = lo + (hi - lo) * 0.381966
    m2 = lo + (hi - lo) * 0.618034
    if J_of_H(m1) < J_of_H(m2):
        lo = m1
    else:
        hi = m2
Hbest = 0.5 * (lo + hi)
print("   best H (1-D scan) = %.9f  J = %.12f   (compare candidate J = %.12f)"
      % (Hbest, J_of_H(Hbest), L.gen_value(g)))
