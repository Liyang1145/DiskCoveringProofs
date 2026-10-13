"""Exact inner-core circle-capacity cut: n21 boundary cell count at most 15."""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import importlib.util
import json

ROOT = Path(__file__).resolve().parent
EV = ROOT/"evidence"
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def main():
    constants = json.loads((EV/"angle-constants.json").read_text())
    assert constants["verified"]
    upper = F(constants["radius_upper"])
    core = 1-2*upper
    assert core > upper > 0
    source = ROOT.parent/"n13-global/independent_checks.py"
    spec = importlib.util.spec_from_file_location("n21_core_capacity_trig",source)
    trig = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(trig)
    _,sine = trig.trig(F(1,10)) # sin(pi/5)
    margin = F(sine[0],trig.S60)-upper/core
    assert margin > 0
    result = {"verified":True,"N":21,"radius_upper":str(upper),
              "core_radius_at_upper":str(core),"upper_core_radius_ratio":str(upper/core),
              "strict_margin_sin_pi_over_five":str(margin),
              "minimum_interior_cells":6,"minimum_boundary_cells":12,"maximum_boundary_cells":15,
              "remaining_families":[[b,21-b] for b in range(12,16)],
              "excluded_boundary_counts":[16,17,18,19,20],
              "scope":"necessary reduction of arbitrary covers, not exclusion of every auxiliary graph realization",
              "global_optimality_proved":False,
              "constants_sha256":hashlib.sha256((EV/"angle-constants.json").read_bytes()).hexdigest()}
    (EV/"core-capacity-cut-verified.json").write_text(json.dumps(result,indent=2),encoding="utf8")
    print("N21 arbitrary-cover core-circle cut: at least 6 interior cells; 12<=B<=15",flush=True)


if __name__ == "__main__":
    main()
