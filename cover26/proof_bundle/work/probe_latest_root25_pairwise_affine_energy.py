"""Test a new exact minorant on actual latest OPEN leaves; never edit forests."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import n26_pairwise_affine_energy as affine
import n26_full_candidate_face_energy as full
import n26_typed_arithmetic_context as codec
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-leaves", type=int, default=16)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists() or not 1 <= args.max_leaves <= 686:
        raise ValueError("preserve existing experiment; invalid actual leaf budget")
    root25 = Path("outputs/n26-candidate-root25-checked-support-cost-forest-diagnosis-v3.json")
    controls25 = Path("outputs/n26-candidate-root25-checked-support-cost-independent-controls-v3.json")
    root28 = Path("outputs/n26-candidate-root28-grown-full134rod-intersection-forest-diagnosis-v9.json")
    controls28 = Path("outputs/n26-candidate-root28-grown-full134rod-intersection-independent-controls-v1.json")
    resource = Path("outputs/n26-original-candidate-arithmetic-context-v1")
    source = Path("outputs/n26-current-candidate-owned-forest-v8")
    paths = [root25, controls25, root28, controls28, resource/"VERIFIED.json",
             resource/"CONTEXT.json", source/"VERIFIED.json", source/"PENDING-ANGLES.json"]
    digests = {str(path): binding.sha(path) for path in paths}
    context_report = binding.read(resource/"VERIFIED.json")
    if (context_report["files"]["CONTEXT.json"] != digests[str(resource/"CONTEXT.json")]
            or context_report["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
            or context_report["files"]["n26_typed_arithmetic_context.py"] != binding.sha(codec.__file__)):
        raise ValueError("fixed DATA context changed")
    model_data = codec.gate(binding.read(resource/"CONTEXT.json")["typed_context"])
    original = model_data["original"]
    model = full.model_gate(original["data"][0], original["reference"], original["data"][3])
    first, first_controls = binding.read(root25), binding.read(controls25)
    second, second_controls = binding.read(root28), binding.read(controls28)
    if (first_controls["diagnosis_sha256"] != digests[str(root25)]
            or second_controls["diagnosis_sha256"] != digests[str(root28)]
            or first["source_OPEN_index"] != 25 or second["source_OPEN_index"] != 28
            or first["verified"] is not False or second["verified"] is not False
            or first_controls["verified"] is not False or second_controls["verified"] is not False
            or first["new_geometric_payments"] != 0 or second["new_geometric_payments"] != 0
            or len(first["pending_closed_leaf_boxes"]) != 686):
        raise ValueError("actual latest arithmetic forests/control associations changed")
    accepted = binding.read(source/"VERIFIED.json")
    pending = binding.read(source/"PENDING-ANGLES.json")
    actual_row = next(row for row in pending if row["index"] == 25)
    if (actual_row != first["actual_source_closed_box"]
            or accepted["files"]["PENDING-ANGLES.json"] != digests[str(source/"PENDING-ANGLES.json")]
            or first["source_file_sha256"]["PENDING-ANGLES.json"] != digests[str(source/"PENDING-ANGLES.json")]):
        raise ValueError("root25 entire source identity changed")
    kernels = [full.kernel_gate(model, item["kernel_certificate"])
               for item in second["full134rod_supports"]]
    arcs = binding.force.load_trig(resource)[0]
    module_paths = [Path(module.__file__) for module in (affine, full, codec, binding)]
    digests.update({str(path): binding.sha(path) for path in module_paths})
    radius = F(original["radius"])
    tiny = original["cap"]["known_candidate_tiny_angle_cells"]
    for kernel in kernels:
        data = affine.prepare(kernel, original["matrix"], [p[0] for p in tiny],
                              [p[1] for p in tiny], arcs)
        _, result, _ = affine.suggest(data, original["matrix"], radius)
        if result is not None and result["arithmetic_strict_entire_closed_leaf"]:
            raise AssertionError("new minorant excludes the known feasible candidate control")
    leaves = first["pending_closed_leaf_boxes"]
    if args.max_leaves < len(leaves):
        selected = [leaves[k*len(leaves)//args.max_leaves] for k in range(args.max_leaves)]
    else:
        selected = leaves
    results, checks = [], 0
    for leaf in selected:
        if first["nodes"][leaf["index"]] != {"kind": "OPEN"}:
            raise ValueError("selected box is not an actual newest OPEN leaf")
        trials = []
        for index, kernel in enumerate(kernels):
            data = affine.prepare(kernel, original["matrix"], leaf["lower"], leaf["upper"], arcs)
            checks += affine.independent_point_checks(data, arcs)
            certificate, result, numerical = affine.suggest(data, original["matrix"], radius)
            trials.append({"full_support_index": index, "certificate": certificate,
                           "exact_entire_closed_leaf_result": result,
                           "numerical_suggestion_NOT_proof": numerical})
        strict = any(trial["exact_entire_closed_leaf_result"] is not None
                     and trial["exact_entire_closed_leaf_result"]["arithmetic_strict_entire_closed_leaf"]
                     for trial in trials)
        results.append({"actual_root25_v3_OPEN_leaf": leaf, "trials": trials,
                        "fresh_exact_whole_leaf_strict": strict})
        print(json.dumps({"actual_latest_root25_OPEN_leaf": leaf["index"],
                          "fresh_exact_whole_leaf_strict": strict,
                          "verified": False, "new_geometric_payments": 0}), flush=True)
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("input changed during actual latest-leaf experiment")
    report = {
        "schema": "N26-actual-latest-root25-pairwise-affine-minorant-experiment-v1",
        "verified": False, "source_OPEN_index": 25,
        "actual_latest_root25_pending_leaves": len(leaves),
        "actual_latest_root25_leaves_tested": len(selected),
        "fresh_exact_whole_closed_leaves_strict": sum(item["fresh_exact_whole_leaf_strict"] for item in results),
        "independent_pair_endpoint_midpoint_line_checks": checks,
        "known_feasible_candidate_control_not_excluded": True,
        "full134rod_kernels_freshly_reconstructed": len(kernels),
        "input_sha256": digests, "results": results,
        "all_existing_forests_nodes_supports_ledgers_and_payments_UNMODIFIED": True,
        "resource_and_root28_supports_are_arithmetic_DATA_ONLY": True,
        "complete_latest_source_geometry_replay_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: report[key] for key in (
        "actual_latest_root25_leaves_tested", "fresh_exact_whole_closed_leaves_strict",
        "independent_pair_endpoint_midpoint_line_checks", "candidate_whole_roots_removed")},
        indent=2), flush=True)


if __name__ == "__main__":
    main()
