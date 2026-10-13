"""Arithmetic-only controls; no source replay and no geometric payments."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import n26_signed_hull_energy_minorant as hull
from n26_sharp_radius_constraints import SCALE
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    known = [
        ((-2, 3, 1, 1, -2), F(-1, 4)),
        ((-2, 3, -1, -1, -2), F(-1, 4)),
        ((-2, 3, -2, 1, -2), F(-1)),
        ((1, 3, -4, -2, -2), F(-4)),
        ((-3, -1, 2, 4, -2), F(-4)),
        ((-2, 3, 1, 1, 2), F(-6)),
        ((-2, 3, -1, 1, 0), F(-3)),
        ((0, 0, -1, 1, -2), F(0)),
    ]
    for parameters, expected in known:
        if hull.coordinate_minimum(*parameters) != expected:
            raise AssertionError(("signed-coordinate exact known minimum", parameters))
    samples = 0
    for a, c in ((-3, -1), (-2, 3), (0, 0), (1, 4)):
        for gl, gu in ((-3, -2), (-2, 1), (0, 0), (1, 4)):
            for eta in (-4, -1, 0, 1, 4):
                minimum = hull.coordinate_minimum(a, c, gl, gu, eta)
                for i in range(101):
                    point = F(a) + F(i, 100) * (c - a)
                    value = min(gl * point, gu * point) - F(eta) * point**2 / 2
                    if minimum > value:
                        raise AssertionError("coordinate exact minorant exceeds a rational sample")
                    samples += 1
    matrix = [[0, SCALE // 4], [SCALE // 4, 0]]
    # Reference outside the target box is permitted only via the closed hull.
    ref, lo, hi, hull_lo, hull_hi = hull.hull_gate(
        [F(0)], [F(1, 10)], [F(1, 5)], matrix)
    if hull_lo != [F(0)] or hull_hi != [F(1, 5)]:
        raise AssertionError("outside-reference closed hull was not formed")
    minimum, _ = hull.support(
        ref, lo, hi, matrix, [(F(0), F(0)), (F(-2), F(-1))],
        [F(-4)], {"q": 3, "terms": [[0, 1, "4"]]})
    for i in range(101):
        x = F(1, 10) + F(i, 1000)
        if minimum > min(-2*x, -x) + 2*x*x:
            raise AssertionError("difference dual sign or target-domain support is invalid")
    rejected = []

    def reject(name, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, ZeroDivisionError):
            rejected.append(name)
        else:
            raise AssertionError("invalid signed-hull input accepted: " + name)

    reject("reversed-coordinate-domain",
           lambda: hull.coordinate_minimum(1, -1, 0, 1, -2))
    reject("reversed-gradient-interval",
           lambda: hull.coordinate_minimum(-1, 1, 1, 0, -2))
    reject("reference-outside-necessary-difference-polytope",
           lambda: hull.hull_gate([F(1, 2)], [F(1, 10)], [F(1, 5)], matrix))
    reject("target-box-dimension-changed",
           lambda: hull.hull_gate([F(0)], [], [F(1, 5)], matrix))
    for name, dual in (
        ("negative-difference-multiplier", {"q": 1, "terms": [[0, 1, "-1"]]}),
        ("duplicate-difference-multiplier", {"q": 1, "terms": [[0, 1, "1"], [0, 1, "1"]]}),
        ("nonpositive-dual-scale", {"q": 0, "terms": []}),
        ("self-difference-multiplier", {"q": 1, "terms": [[1, 1, "1"]]}),
        ("out-of-range-difference-index", {"q": 1, "terms": [[0, 2, "1"]]}),
    ):
        reject(name, lambda dual=dual: hull.support(
            ref, lo, hi, matrix, [(F(0), F(0)), (F(-2), F(-1))], [F(-4)], dual))
    reject("generic-kernel-relabelled-as-original-candidate",
           lambda: hull.bound({"B": 16, "vertices": 62, "weights": [1] * 92},
                              matrix, [0], [1], {}, F(1, 4), None))
    report = {
        "schema": "N26-signed-hull-arithmetic-controls-v1",
        "arithmetic_controls_passed": True,
        "exact_known_coordinate_minima_checked": len(known),
        "rational_coordinate_value_samples_checked": samples,
        "outside_target_reference_hull_formed_and_difference_gate_passed": True,
        "exact_nonnegative_dual_sign_and_target_support_checked": True,
        "rejection_controls_passed": rejected,
        "arithmetic_only_not_a_geometry_or_current_source_replay": True,
        "new_geometric_payments": 0,
        "tested_signed_hull_module_sha256": binding.sha(hull.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
