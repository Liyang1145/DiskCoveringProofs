"""print_numbers.py -- readable summary of coverage-audit/out/coverage-audit.json"""
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
r = json.loads((HERE / "out" / "coverage-audit.json").read_text(encoding="utf-8"))
n = r["numbers"]

print("== slack faces: my R^2 (via abc/4K) vs recorded ==")
ok = True
for row in n["slack_rows"]:
    mine_lo, mine_hi = F(row["rad2"][0]), F(row["rad2"][1])
    rlo, rhi = F(row["recorded_rad2"][0]), F(row["recorded_rad2"][1])
    inter = not (mine_hi < rlo or rhi < mine_lo)
    ok &= inter and row["margin"] != "0"
    print("  face %s  mine=[%.17g, %.17g]  rec=[%.17g, %.17g]  overlap=%s  "
          "margin_mine=%.6e  margin_rec=%.6e"
          % (row["face"], float(mine_lo), float(mine_hi), float(rlo), float(rhi),
             inter, float(F(row["margin"])), float(F(row["recorded_margin"]))))
print("all slack overlaps:", ok)

print()
print("== active faces: [dist^2 - r^2] intervals via the claimed witnesses ==")
for row in n["active_rows"]:
    vals = [(float(F(a)), float(F(b))) for a, b in row["dist2_minus_r2"]]
    print("  face %s ok=%s widths=%s" % (row["face"], row["ok"],
                                         ["%.2e" % (b - a) for a, b in vals]))

print()
print("== constants ==")
print("  b =", n["b"])
print("  d =", n["d"])
print("  r =", n["r"])
print("  cos alpha =", [float(F(x)) for x in n["cos_alpha"]], " (in (1/2,1) required)")
print("  r^2 =", [float(F(x)) for x in n["r2"]])
print("  clear_denoms ratios:", n["clear_denoms_ratios"])

print()
rows = n["outside_rows"]
print("outside samples: n=%d  proj&mono all = %s"
      % (len(rows), all(x["proj_ok"] and x["monotone"] for x in rows)))
print("  min_dist^2 strictly below r^2 in all samples:",
      all(x["min_dist2_hi_lt_r2_lo"] for x in rows))
print()
print("checks:", r["summary"])
