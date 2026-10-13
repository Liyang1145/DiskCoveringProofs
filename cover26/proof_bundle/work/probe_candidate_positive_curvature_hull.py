"""Unaccepted positive-curvature hull diagnosis on the fixed original model.

This reads the accepted arithmetic resource for exploration only. It does NOT
replace the complete latest-source gate, import new current ownership, pay a
leaf/root, or issue a candidate geometry acceptance.
"""

import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

import numpy as np

from audit_prefix_partition import linux
import n26_typed_arithmetic_context as codec
import n26_current_candidate_layer_identity as identity
import n26_quadratic_energy_minorant as energy
from n26_sharp_radius_constraints import tighten
import verify_conditional_force_stage as binding


RESOURCE_SHA = "935d336bd4b2cbac1ff819be3b846ca7512ed1c94b8b9122b30833a246694e8a"


def matrix_digest(matrix):
    text = json.dumps([[str(x) for x in row] for row in matrix],
                      separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(text).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "report"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--indices", nargs="+", type=int, default=[41, 45, 48, 959])
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    resource = binding.read(args.resource / "VERIFIED.json")
    if (
        binding.sha(args.resource / "VERIFIED.json") != RESOURCE_SHA
        or binding.sha(args.resource_replay) != RESOURCE_SHA
        or binding.read(args.resource_replay) != resource
        or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
        or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
    ):
        raise ValueError("fixed arithmetic resource identity or zero-source scope changed")
    for name in ("CONTEXT.json", "n26_typed_arithmetic_context.py"):
        if binding.sha(args.resource / name) != resource["files"][name]:
            raise ValueError("fixed model or codec bytes changed")
    if binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]:
        raise ValueError("diagnosis executed a different typed data codec")
    context = binding.read(args.resource / "CONTEXT.json")
    model = codec.gate(context["typed_context"])
    original, kernel = model["original"], model["original_kernel"]
    if (
        kernel["B"] != 16 or kernel["vertices"] != 62
        or len(kernel["weights"]) != 92
        or kernel["original_candidate_92_rod_46_free_vertex_kernel"] is not True
    ):
        raise ValueError("diagnosis requires the original grounded 92-rod model")
    current_sha = binding.sha(args.current_audit)
    current = binding.read(args.current_audit)
    layer = identity.gate(current, current_sha, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("diagnosis changed the current exact radius")
    pending = binding.read(args.source / "PENDING-ANGLES.json")
    selected = [row for row in pending if row["index"] in args.indices]
    if {row["index"] for row in selected} != set(args.indices):
        raise ValueError("a requested root is absent or already discharged")
    matrix = original["matrix"]
    tiny = [tuple(map(F, pair))
            for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    tiny_box = tighten(matrix, [a for a, _ in tiny], [b for _, b in tiny])
    if tiny_box is None:
        raise ValueError("known tiny angle cells lost their necessary domain")
    reference = [F(0), *tiny_box[0]]
    energy.reference_gate(reference[1:], tiny_box[0], tiny_box[1], matrix)
    arcs = binding.force.load_trig(args.resource)[0]
    free_start = 10
    results = []
    for row in selected:
        actual = tighten(matrix, row["sharp_lower"], row["sharp_upper"])
        if actual is None:
            raise ValueError("a retained source root unexpectedly has empty sharp domain")
        lower, upper = actual
        hull_lower = [min(a, r) for a, r in zip(lower, reference[1:])]
        hull_upper = [max(b, r) for b, r in zip(upper, reference[1:])]
        hessian = energy.hessian_minorant(kernel, matrix, hull_lower, hull_upper, arcs)
        approximate = np.array([[float(value) for value in line] for line in hessian])
        full_min = float(np.linalg.eigvalsh(approximate)[0])
        free_block = approximate[free_start:, free_start:]
        free_min = float(np.linalg.eigvalsh(free_block)[0])
        record = {
            "source_OPEN_index": row["index"],
            "actual_source_closed_box": row,
            "reference_outside_actual_closed_box": any(
                not a <= r <= b for a, b, r in zip(lower, upper, reference[1:])),
            "convex_hull_lower": list(map(str, hull_lower)),
            "convex_hull_upper": list(map(str, hull_upper)),
            "outward_Hessian_minorant_sha256": matrix_digest(hessian),
            "floating_full_Hessian_minimum": full_min,
            "floating_last_five_block_minimum": free_min,
            "floating_eigenvalues_not_geometric_proof": True,
            "exact_signed_diagonal_curvature_check_passed": False,
        }
        if free_min > 1e-12:
            beta = F(max(1, int(free_min / 4 * 10**12)), 10**12)
            aa = approximate[:free_start, :free_start]
            ab = approximate[:free_start, free_start:]
            schur = aa - ab @ np.linalg.solve(
                free_block - float(beta) * np.eye(5), ab.T)
            alpha_float = max(0., -float(np.linalg.eigvalsh(schur)[0])) * 1.02 + 1.
            alpha = F(int(alpha_float * 10**8) + 1, 10**8)
            for attempt in range(6):
                signed = [alpha] * free_start + [-beta] * (15 - free_start)
                tested = [
                    [value + (signed[i] - F(15, energy.ROUND_GRID) if i == j else 0)
                     for j, value in enumerate(line)]
                    for i, line in enumerate(hessian)
                ]
                try:
                    pivots = energy.positive_ldl(tested)
                except ValueError:
                    alpha = 2 * alpha + 1
                else:
                    record.update(
                        exact_signed_diagonal_curvature_check_passed=True,
                        fixed_anchor_negative_allowance=str(alpha),
                        last_five_positive_curvature=str(beta),
                        spectral_rounding_error_charged=str(F(15, energy.ROUND_GRID)),
                        exact_LDL_minimum_pivot=str(min(pivots)),
                        tested_signed_matrix_sha256=matrix_digest(tested),
                        attempts=attempt + 1,
                    )
                    break
        results.append(record)
        print(json.dumps({key: value for key, value in record.items()
                          if key not in ("actual_source_closed_box",
                                         "convex_hull_lower", "convex_hull_upper")}),
              flush=True)
    if binding.sha(args.current_audit) != current_sha:
        raise ValueError("actual current snapshot changed during diagnosis")
    report = {
        "schema": "N26-unaccepted-positive-curvature-hull-diagnosis-v1",
        "verified": False,
        "fixed_resource_acceptance_sha256": RESOURCE_SHA,
        "resource_context_sha256": binding.sha(args.resource / "CONTEXT.json"),
        "actual_current_audit_sha256": current_sha,
        "actual_latest_layer_identity_only": layer,
        "reference_feasible_in_known_tiny_domain": True,
        "reference_turns": list(map(str, reference[1:])),
        "original_92_rods_and_52_coordinate_LOCAL_allowance_unchanged": True,
        "results": results,
        "exact_curvature_matrix_checks_are_not_leaf_or_root_payments": True,
        "full_latest_model_source_replay_not_performed_here": True,
        "all_resource_historical_dependencies_not_rehashed_here": True,
        "needs_independent_hull_Taylor_lemma_and_actual_reference_gradient_dual": True,
        "needs_actual_latest_source_model_identity_and_full_ownership_gate": True,
        "new_geometric_payments": 0,
        "current_candidate_roots_removed": 0,
        "global_lower_bound_proved": False,
        "global_optimality_proved": False,
        "executed_probe_sha256": binding.sha(__file__),
        "modules": {linux(Path(module.__file__)): binding.sha(module.__file__)
                    for module in (codec, energy, identity, binding)},
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "diagnosis_completed": True,
        "exact_signed_curvature_checks": sum(
            row["exact_signed_diagonal_curvature_check_passed"] for row in results),
        "roots_examined": len(results),
        "new_geometric_payments": 0,
        "verified": False,
    }), flush=True)


if __name__ == "__main__":
    main()
