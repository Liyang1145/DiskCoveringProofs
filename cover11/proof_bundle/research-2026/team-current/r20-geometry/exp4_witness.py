"""Verify and store the two decisive non-flat witnesses of the general patch domain.

W1 = the CERTIFIED cover's own local data (cand_local_data.json)
W2 = the profile-family maximum at alpha2 = 2.7416 (exp3_profile.json)
Both are re-checked: all general-chart margins, coordinate consistency, J value.
"""
import json, math, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import r20_lib as L

PI, R = L.PI, L.R
THRESH = 28.10704541577262956809
prof = json.load(open(HERE / "exp3_profile.json"))
p2 = [q for q in prof if q.get("kind") == "profile" and abs(q["a2"] - 2.741593) < 1e-6][0]

d0 = json.load(open(HERE / "cand_local_data.json"))
base = dict(t=d0["t"], a1=d0["a1"], u1=d0["u1"], s1=d0["t"], a2=0.0, s2=d0["t"],
            a3=d0["a3"], v3=d0["v3"], A=0.0, H=0.0)

W = {}
# --- W1 -----------------------------------------------------------------------------
w1 = dict(base, a2=d0["a2"], A=d0["A"], H=d0["H"])
W["W1_certified_cover_local"] = w1
# --- W2 -----------------------------------------------------------------------------
w2 = dict(base, a2=p2["a2"], A=p2["A"], H=p2["H"])
W["W2_profile_max"] = w2

for name, p in W.items():
    g = L.gen_args(p)
    names, mg = L.gen_margins(p, g)
    c = L.consistency(p, g)
    J = L.gen_value(g)
    print("== %s" % name)
    print("   a2=%.12f  pi-a2=%.9f   A=%.9f  B=%.9f  H=%.9f" % (p["a2"], PI - p["a2"], g["A"], g["B"], p["H"]))
    print("   b1=%.9f b2=%.9f   J = %.12f   J-T = %+.6e" % (g["b1"], g["b2"], J, J - THRESH))
    print("   min margin %+.3e (%s)" % (min(mg), names[int(np.argmin(mg))]))
    print("   tight constraints:", [(n, "%.1e" % m) for n, m in zip(names, mg) if m < 1e-6])
    print("   consistency: |c1-c2|-D1 = %+.2e ; angle(c1,c3)@c2 vs -(A+B) : %.12f vs %.12f"
          % (c["|c1-c2|"] - c["D1"], c["angle(c1,c3)@c2"], -(g["A"] + g["B"])))
    print("   |c2| = %.12f  <= s(r) = %.12f ; hubnorm=%.12f <= 1-r=%.12f"
          % (c["|c2|"], c["s(r)"], g["hubnorm"], 1 - g["r"]))
    print()

json.dump({k: {kk: float(vv) for kk, vv in v.items()} for k, v in W.items()},
          open(HERE / "witness_nonflat.json", "w"), indent=1)
print("wrote witness_nonflat.json")

# also: how does J vary with alpha2 along this family (the growth direction)?
print("profile family (J vs alpha2), from exp3_profile.json:")
for q in prof:
    if q.get("kind") == "profile":
        print("   alpha2=%.6f  pi-alpha2=%.6f  J=%.9f  J-T=%+.4e" % (q["a2"], PI - q["a2"], q["J"], q["J"] - THRESH))
