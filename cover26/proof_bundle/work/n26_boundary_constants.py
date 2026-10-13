import argparse
import hashlib
import importlib.util
import json
from fractions import Fraction as F
from pathlib import Path


def load_exact_arcs(path: Path):
    spec = importlib.util.spec_from_file_location("n26_exact_arcs", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--arcs", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    arcs = load_exact_arcs(args.arcs)
    U = F(239146311738101, 10**15)
    D = 10**7
    caps = [768677, 1587443, 2546859, 4058615]
    margins = []
    for k, cap in enumerate(caps, 1):
        lower = F(arcs.sincos_turn(F(cap, 2 * D))[1][0], arcs.SCALE)
        gap = lower - k * U
        assert gap > 0
        margins.append(str(gap))
    direct_lower = F(arcs.sincos_turn(F(1, 26))[1][0], arcs.SCALE)
    assert direct_lower > U
    ratio = U / (1 - 2 * U)
    assert ratio < F(1, 2)
    circle_gap = D - 13 * caps[0]
    assert circle_gap > 0
    families = [[14, 12], [15, 11], [16, 10], [17, 9], [18, 8]]
    report = {
        "verified": True,
        "schema": "N26-boundary-angle-and-family-scope-v1",
        "N": 26,
        "radius_upper": str(U),
        "angle_scale": D,
        "angle_caps_two_four_six_eight": caps,
        "positive_exact_sine_margins": margins,
        "direct_boundary_lower_sine_gap": str(direct_lower - U),
        "strict_integer_circle_budget_gap": circle_gap,
        "normalized_core_radius_upper": str(ratio),
        "strict_half_core_gap": str(F(1, 2) - ratio),
        "minimum_boundary_cells": 14,
        "minimum_interior_cells": 8,
        "maximum_boundary_cells": 18,
        "necessary_boundary_internal_families": families,
        "internal_bound_source": "self-contained elementary r_D(7) >= 1/2",
        "global_optimality_proved": False,
        "source_exact_arcs_sha256": sha(args.arcs),
    }
    args.output.mkdir(parents=True)
    (args.output / "CONSTANTS.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
