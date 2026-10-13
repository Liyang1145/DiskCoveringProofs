"""Chart interface check on the certified candidate's local patch.

The general chart must reproduce (up to the canonical rotation of the frame):
  * the closure half-angles b1,b2,
  * the general identity  A+B = pi + b1 + b2 - alpha2   (flat case: A+B = b1+b2),
  * all pairwise distances among {c1,c2,c3,hub} and the angles at c2.
"""
import json, io, math, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import r20_lib as L

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
obj = json.load(io.open(ROOT / "n11/upper/certified_object.json", encoding="utf-8"))
sc = 10 ** int(obj["decimals"])
C = np.array([[int(a), int(b)] for a, b in obj["centers_scaled_1e17"]], dtype=float) / sc
d = json.load(open(HERE / "cand_local_data.json"))
p = dict(t=d["t"], a1=d["a1"], u1=d["u1"], s1=d["s1"], a2=d["a2"], s2=d["s2"],
         a3=d["a3"], v3=d["v3"], A=d["A"], H=d["H"])
g = L.gen_args(p)
print("gen_args:", "ok" if g else "FAIL")
print("chart b1,b2 = %.15f %.15f   geom = %.15f %.15f" % (g["b1"], g["b2"], d["b1_geom"], d["b2_geom"]))

# actual local points
c2 = C[1]
c1 = C[7]
c3 = C[8]
hub = C[2]
G = g["coords"]


def dist(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])


print("\ndistances (chart vs geometry, /R):")
pairs = [("c1-c2", (c1, c2), (G["c1"], G["c2"])),
         ("c2-c3", (c2, c3), (G["c2"], G["c3"])),
         ("c2-hub", (c2, hub), (G["c2"], G["c9"])),
         ("c1-hub", (c1, hub), (G["c1"], G["c9"])),
         ("c3-hub", (c3, hub), (G["c3"], G["c9"])),
         ("c1-c3", (c1, c3), (G["c1"], G["c3"]))]
for nm, (a, b), (x, y) in pairs:
    print("  %-7s geom %.12f   chart %.12f" % (nm, np.linalg.norm(np.array(a) - np.array(b)) / L.R, dist(x, y) / L.R))


def angle_at(o, a, b):
    u = np.array(a) - np.array(o)
    v = np.array(b) - np.array(o)
    return math.atan2(abs(u[0] * v[1] - u[1] * v[0]), float(u.dot(v)))


print("\nangle at c2 between c1 and hub : geom %.12f chart %.12f (A=%.12f)"
      % (angle_at(c2, c1, hub), angle_at(G["c2"], G["c1"], G["c9"]), d["A"]))
print("angle at c2 between hub and c3: geom %.12f chart %.12f"
      % (angle_at(c2, hub, c3), angle_at(G["c2"], G["c9"], G["c3"])))
print("angle at c2 between c1 and c3: geom %.12f chart %.12f   pi+b1+b2-alpha2 %.12f"
      % (angle_at(c2, c1, c3), angle_at(G["c2"], G["c1"], G["c3"]), L.PI + g["b1"] + g["b2"] - p["a2"]))
print("hub norm: geom %.12f chart %.12f  1-r=%.12f" % (np.linalg.norm(hub), np.linalg.norm(G["c9"]), 1 - L.R * d["t"]))

names, mg = L.gen_margins(p, g)
print("\nmin margin %.3e  (%s)" % (min(mg), names[int(np.argmin(mg))]))
J = L.gen_value(g)
print("J(candidate local data) = %.12f" % J)
print("threshold pi-(const+sum22) = 28.10704541577262956809  -> J-thr = %+.6e" % (J - 28.10704541577262956809))
