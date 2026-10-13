"""Synthetic projection controls only; zero original geometry is credited."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import n26_typed_arithmetic_context as codec
import verify_original_candidate_arithmetic_context as checker


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    frame = {
        "cap": {"typed": (True, 1, F(1), -0.0)},
        "reference": {"edges": [[k, k + 1] for k in range(92)]},
        "matrix": [[F(1), F(0)]] * 16, "radius": F(3, 13),
        "data": (None, [], {}, "fixture",
                 {"unrestricted_center_neighbourhood_halfwidth_before_rotation": "7/800000"},
                 "not projected"),
    }
    kernel = {"B": 16, "vertices": 62, "original_candidate_92_rod_46_free_vertex_kernel": True}
    values = (None, None, {"fixture_only": True}, frame, None, kernel)
    model = checker.projection(values)
    expected = codec.pack(model)
    restored = checker.payload_gate(expected, expected)
    if (
        codec.pack(restored) != expected
        or type(restored["original"]["data"]) is not tuple
        or len(restored["original"]["data"]) != 5
        or type(restored["original"]["cap"]["typed"][0]) is not bool
        or type(restored["original"]["cap"]["typed"][1]) is not int
        or type(restored["original"]["cap"]["typed"][2]) is not F
    ):
        raise AssertionError("resource projection lost exact types or included unselected data")
    controls = checker.rejection_controls(expected, {"fixture_positive": True, "exact": "7/800000"})
    if len(controls) != 13:
        raise AssertionError("resource failed to reject all synthetic altered models")
    report = {
        "schema": "N26-original-arithmetic-resource-schema-regression-v1",
        "synthetic_exact_projection_roundtrip_passed": True,
        "invalid_resource_model_controls_rejected": controls,
        "synthetic_only_not_an_actual_legacy_geometry_replay": True,
        "new_geometric_candidate_payments": 0, "current_candidate_roots_removed": 0,
        "tested_resource_verifier_sha256": checker.sha(checker.__file__),
        "executed_test_sha256": checker.sha(__file__),
        "global_lower_bound_proved": False, "global_optimality_proved": False,
    }
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
