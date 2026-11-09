"""Replay every certificate used for the reported bounds."""

import json
import os
import subprocess
import sys
from fractions import Fraction as Q
from pathlib import Path

from verify_template import root_box


ROOT = Path(__file__).resolve().parent


def run(script, *args):
    env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}
    subprocess.run([sys.executable, str(ROOT / script), *args], cwd=ROOT, env=env, check=True)


def check_branches(name, expected, disks=26):
    entries = json.loads((ROOT / name).read_text(encoding="utf-8"))
    if any(e.get("disks", 26) != disks for e in entries):
        raise ValueError(f"Wrong disk count in {name}")
    if any("middle_split" in e for e in entries):
        raise ValueError(f"A middle-population split requires a separate completeness check: {name}")
    if name == "lower_22862_core.json" and any(e.get("participants") != 8 for e in entries):
        raise ValueError("The central-count branches require eight participants")
    observed = [(e["k"], e.get("low"), Q(e["r_min"]), Q(e["r_max"])) for e in entries]
    want = [(k, low, Q(rmin), Q(rmax)) for k, low, rmin, rmax in expected]
    if sorted(observed) != sorted(want):
        raise ValueError(f"Incomplete branch certificate: {name}")


def main():
    run("verify_upper.py", "upper.json", "--radius", "234701/1000000")
    run("verify_upper.py", "upper.json")
    run("verify_upper.py", "upper_refined.json")
    run("verify_eight_constants.py")
    check_branches("lower_radial.json", [(k, None, ".2238", ".2238") for k in range(14, 18)])
    run("verify_radial.py", "lower_radial.json")
    check_branches("radial_2265.json", [(k, None, ".2265", ".2265") for k in (14, 17)])
    run("verify_radial.py", "radial_2265.json")
    run("verify_fan.py")
    run("verify_seam.py")

    certificates = [
        ("lower_2275.json", [(k, None, ".2275", ".2275") for k in (15, 16, 17)], 26),
        ("lower_22835.json", [(k, None, ".22835", ".22835") for k in (15, 16, 17)], 26),
        ("branch_k14_low4.json", [(14, 4, ".23185", ".234701")], 26),
        ("branch_k15_22862.json", [(15, None, ".2275", ".22862")], 26),
        ("branch_k15_22905.json", [(15, None, ".22862", ".22905")], 26),
        ("branch_k16_22846.json", [(16, None, ".22846", ".22846")], 26),
        ("lower_22855_split.json", [(16, low, ".22855", ".22855") for low in (0, 1)], 26),
        ("lower_22861.json", [(16, low, ".22861", ".22861") for low in (0, 1)], 26),
        ("lower_22862_core.json", [(16,low,".22862",".22862") for low in (0,1)],26),
        ("branch_k17_22765.json", [(17, None, ".22765", ".22765")], 26),
        ("branch_k17_2287.json", [(17, None, ".2287", ".2287")], 26),
        ("lower25_2328.json", [(k, None, ".2328", ".2328") for k in (15, 16)], 25),
    ]
    for name, expected, disks in certificates:
        check_branches(name, expected, disks)
        run("verify_joint.py", name)

    run("verify_template.py")
    run("verify_local.py")
    run("verify_candidate_cell.py")
    center, width, _ = root_box()
    u = Q(json.loads((ROOT / "upper_refined.json").read_text(encoding="utf-8"))["radius"])
    if center[0] + width >= u:
        raise ValueError("Algebraic covering radius is not certified below the rational upper bound")
    print("PASS: analytic bounds, exact covers and local candidate certificates")


if __name__ == "__main__":
    main()
