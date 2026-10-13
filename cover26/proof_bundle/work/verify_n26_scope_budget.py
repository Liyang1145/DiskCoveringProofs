"""Fresh arithmetic gate for the written N26 boundary-count argument.

The output binds the manuscript and constants; it explicitly does not certify
transport of arbitrary covers to the enumerator's simple triangular disks.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path

from audit_prefix_partition import expect_rejection, publish, sha


WORK = Path(__file__).resolve().parent
ARCS = Path(
    "C:/热爱单机但萌新/_incoming-local-math-20261004/recovered-20261004/workspace/"
    "research-2026/disk-cover-proof-library/external/pinned/cover20/proof_bundle/core/exact_arcs.py"
)


def gate(constants, arcs):
    if constants["N"] != 26 or constants["verified"] is not True:
        raise ValueError("wrong order or unverified input")
    U = F(constants["radius_upper"])
    D = constants["angle_scale"]
    caps = constants["angle_caps_two_four_six_eight"]
    if not (0 < U < F(1, 4) and D == 10**7 and len(caps) == 4
            and 0 < caps[0] < caps[1] < caps[2] < caps[3] < D // 2):
        raise ValueError("invalid radius or angular budget")
    alpha = F(3, 2) * (1 - U * U)
    if not (alpha > 0 and alpha * alpha < 2):
        raise ValueError("U does not strictly exceed the exact duplicated n25 radius")
    margins = [
        F(arcs.sincos_turn(F(cap, 2 * D))[1][0], arcs.SCALE) - k * U
        for k, cap in enumerate(caps, 1)
    ]
    if min(margins) <= 0:
        raise ValueError("nonpositive rod-cap sine margin")
    boundary_margin = F(arcs.sincos_turn(F(1, 26))[1][0], arcs.SCALE) - U
    q = U / (1 - 2 * U)
    if not (boundary_margin > 0 and D - 13 * caps[0] > 0 and q < F(1, 2)):
        raise ValueError("boundary or inner-core inequality not strict")
    pairs = [[b, 26 - b] for b in range(14, 26 - 8 + 1)]
    if constants["necessary_boundary_internal_families"] != pairs:
        raise ValueError("wrong counting pairs")
    if constants["source_exact_arcs_sha256"] != sha(ARCS):
        raise ValueError("unbound exact trigonometry source")
    if constants["normalized_core_radius_upper"] != str(q):
        raise ValueError("wrong core ratio")
    if constants["positive_exact_sine_margins"] != list(map(str, margins)):
        raise ValueError("changed margins")
    return {
        "radius_upper": str(U), "root_squared_comparison_gap": str(2 - alpha * alpha),
        "quarter_radius_gap": str(F(1, 4) - U),
        "direct_boundary_sine_margin": str(boundary_margin),
        "core_ratio_upper": str(q), "strict_half_core_margin": str(F(1, 2) - q),
        "rod_caps": caps, "positive_exact_sine_margins": list(map(str, margins)),
        "physical_boundary_internal_count_pairs": pairs,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    constants_path = WORK.parent / "outputs/n26-boundary-constants-v2/CONSTANTS.json"
    proof_path = WORK.parent / "outputs/n26-boundary-family-derivation-v1.md"
    constants = json.loads(constants_path.read_text(encoding="utf-8"))
    spec = importlib.util.spec_from_file_location("fresh_n26_exact_arcs", ARCS)
    arcs = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(arcs)
    checks = gate(constants, arcs)
    negatives = []
    for label, field, value in (
        ("wrong-order", "N", 25),
        ("quarter-threshold-not-strict", "radius_upper", "1/4"),
        ("upper-below-exact-root", "radius_upper", "239146311738/1000000000000"),
        ("cap8-too-small", "angle_caps_two_four_six_eight", [768677, 1587443, 2546859, 3000000]),
        ("missing-count-pair", "necessary_boundary_internal_families", [[14, 12], [18, 8]]),
        ("wrong-core-ratio", "normalized_core_radius_upper", "1/2"),
        ("unverified-input", "verified", False),
    ):
        wrong = deepcopy(constants)
        wrong[field] = value
        expect_rejection(label, lambda: gate(wrong, arcs), negatives)
    report = {
        "schema": "N26-written-boundary-count-arithmetic-gate-v1",
        "arithmetic_checks_verified": True, **checks,
        "written_count_argument_bound": True,
        "arbitrary_cover_to_simple_disk_enumerator_proved": False,
        "N26_complete_catalog": False, "global_optimality_proved": False,
        "negative_controls_rejected": negatives,
        "files": {str(p): sha(p) for p in (
            Path(__file__), WORK / "audit_prefix_partition.py",
            ARCS, constants_path, proof_path,
        )},
        "scope": "Rational and trigonometric margins for a written counting argument; not formalization or enumeration-transport verification.",
    }
    publish(args.output, report)
    print(json.dumps({"arithmetic_checks_verified": True,
                      "negative_controls": len(negatives),
                      "count_pairs": checks["physical_boundary_internal_count_pairs"],
                      "enumerator_transport_proved": False}, indent=2), flush=True)


if __name__ == "__main__":
    main()
