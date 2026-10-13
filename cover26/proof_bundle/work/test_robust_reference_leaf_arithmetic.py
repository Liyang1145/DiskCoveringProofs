"""Independent real robust-reference leaf checks; no whole-root admission."""

import argparse
import json
from pathlib import Path

import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import probe_robust_positive_support_references as producer
import test_alternative_signed_support_arithmetic as independent
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "diagnosis", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    resource = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != fixed.RESOURCE_SHA
            or binding.sha(args.resource_replay) != fixed.RESOURCE_SHA
            or binding.read(args.resource_replay) != resource
            or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
            or binding.sha(args.resource / "CONTEXT.json") != resource["files"]["CONTEXT.json"]
            or binding.sha(codec.__file__) != resource["files"]["n26_typed_arithmetic_context.py"]):
        raise ValueError("robust-reference arithmetic controls changed model DATA identity")
    original = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])["original"]
    diagnosis = binding.read(args.diagnosis)
    digest = binding.sha(args.diagnosis)
    if (diagnosis["schema"] != "N26-unaccepted-robust-positive-weight-reference-leaf-diagnosis-v1"
            or diagnosis["executed_probe_sha256"] != binding.sha(producer.__file__)
            or diagnosis["verified"] is not False or diagnosis["new_geometric_payments"] != 0
            or diagnosis["candidate_whole_roots_removed"] != 0):
        raise ValueError("robust-reference diagnostic producer or zero-payment scope changed")
    arcs = binding.force.load_trig(args.resource)[0]
    checked = []
    for item in diagnosis["results"]:
        for trial in item["tests"]:
            if not trial["strict_actual_closed_leaf_exclusion"]:
                continue
            adapted = {**trial, "actual_closed_leaf": item["actual_closed_leaf"]}
            result = independent.check(original, arcs, adapted)
            checked.append({"old_OPEN_leaf_index": item["old_OPEN_leaf_index"],
                            "reference_turns": trial["reference_turns"],
                            "reconstructed_exact_result": result})
    if not checked:
        raise ValueError("robust-reference arithmetic controls have no actual strict proof")
    if binding.sha(args.diagnosis) != digest:
        raise ValueError("robust-reference diagnosis changed during reconstruction")
    report = {
        "schema": "N26-independent-robust-reference-closed-leaf-arithmetic-controls-v1",
        "actual_strict_robust_reference_proofs_reconstructed": checked,
        "independent_sine_square_feasible_corner_midpoint_checks": 3*len(checked),
        "diagnosis_sha256": digest, "actual_proper_closed_LEAF_only_NOT_whole_source_root": True,
        "verified": False, "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "complete_latest_source_model_history_geometry_gate_NOT_executed": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "tested_signed_module_sha256": binding.sha(independent.signed.__file__),
        "executed_test_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"robust_reference_independent_arithmetic_checks_completed": True,
                      "actual_strict_proofs": len(checked), "verified": False,
                      "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
