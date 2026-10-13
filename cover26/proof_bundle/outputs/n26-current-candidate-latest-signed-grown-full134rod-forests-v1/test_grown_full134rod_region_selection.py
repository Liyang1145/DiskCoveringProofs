"""Arithmetic-only grown region selection; NOT latest-source ownership."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

import n26_grown_full134rod_region_selection as selection
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as resource_definition
import probe_root_clipped_grown_full134rod_regions as region_producer
import test_root_clipped_grown_full134rod_regions as region_controls
import verify_conditional_force_stage as binding


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "diagnosis", "controls", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    accepted = binding.read(args.resource / "VERIFIED.json")
    if (binding.sha(args.resource / "VERIFIED.json") != resource_definition.RESOURCE_SHA
            or binding.sha(args.resource_replay) != resource_definition.RESOURCE_SHA
            or binding.read(args.resource_replay) != accepted
            or binding.sha(args.resource / "CONTEXT.json") != accepted["files"]["CONTEXT.json"]
            or accepted["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True):
        raise ValueError("grown selection changed arithmetic model DATA")
    original = codec.gate(binding.read(args.resource / "CONTEXT.json")["typed_context"])["original"]
    record, controls = binding.read(args.diagnosis), binding.read(args.controls)
    diagnosis_digest, controls_digest = binding.sha(args.diagnosis), binding.sha(args.controls)
    if (record["executed_probe_sha256"] != binding.sha(region_producer.__file__)
            or controls["schema"] != region_controls.SCHEMA
            or controls["executed_test_sha256"] != binding.sha(region_controls.__file__)
            or controls["diagnosis_sha256"] != diagnosis_digest
            or controls["tested_probe_sha256"] != binding.sha(region_producer.__file__)
            or len(controls["actual_root_subset_source_history_and_zero_payment_guards_rejected"]) != 10
            or controls["source_file_sha256"] != record["source_file_sha256"]
            or controls["verified"] is not False or controls["new_geometric_payments"] != 0):
        raise ValueError("grown selection lacks actual independent entire-region controls")
    table = [{
        "mode": selection.mixed.SUPPORT_MODE,
        "kernel_certificate": item["NEW_full134rod_stress_kernel_certificate"],
        "suggestion_point_turns": item["actual_feasible_reference_turns"],
    } for item in record["results"]]
    row = record["actual_source_closed_box"]
    regions, audit = selection.select(original, binding.force.load_trig(args.resource)[0], row, table, record)
    if len(regions) != 2 or sum(item["fresh_strict"] for item in audit) != 4:
        raise ValueError("actual grown selection omitted or changed a strict stress origin")
    arcs = binding.force.load_trig(args.resource)[0]
    rejected = []

    def reject(label, mutation):
        bad = deepcopy(record)
        mutation(bad)
        try:
            selection.select(original, arcs, row, table, bad)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual grown selection accepted: "+label)

    for label, mutation in (
        ("grown-selection-non_strict-region-promoted", lambda bad: bad["results"][0]["trials"][2].update(
            fresh_exact_strict_closed_region=True)),
        ("grown-selection-largest-region-cached-margin-forged", lambda bad: bad[
            "results"][0]["trials"][1]["NEW_correlated_result"].update(strict_radius_margin="1")),
        ("grown-selection-source-closed-lower-escaped", lambda bad: bad["results"][0]["trials"][0][
            "actual_source_root_clipped_closed_lower"].__setitem__(0, "-100")),
        ("grown-selection-unrequested-width", lambda bad: bad["results"][0]["trials"][0].update(
            requested_root_closed_half_width="1/2")),
        ("grown-selection-proper-region-paid-as-whole", lambda bad: bad["results"][0]["trials"][0].update(
            region_equals_entire_actual_source_root=True)),
        ("grown-selection-old-leaf-clipping-laundered", lambda bad: bad["results"][0]["trials"][0].update(
            old_checked_v7_leaf_boundary_NOT_used_to_clip_this_region=False)),
        ("grown-selection-support-origin-omitted", lambda bad: bad["results"].pop()),
        ("grown-selection-paid-as-current-geometry", lambda bad: bad.update(verified=True, new_geometric_payments=1)),
    ):
        reject(label, mutation)
    if binding.sha(args.diagnosis) != diagnosis_digest or binding.sha(args.controls) != controls_digest:
        raise ValueError("grown selection evidence changed during arithmetic controls")
    report = {
        "schema": "N26-independent-pure-grown-full134rod-region-selection-controls-v1",
        "verified": False, "diagnosis_sha256": diagnosis_digest,
        "actual_grown_region_controls_sha256": controls_digest,
        "actual_selected_widest_strict_closed_regions": regions,
        "all_root_clipped_region_results_freshly_reconstructed": audit,
        "actual_selection_scope_bound_and_false_strictness_controls_rejected": rejected,
        "selection_is_arithmetic_DATA_NOT_latest_forest_source_history_or_geometry_admission": True,
        "all_original_and_NEWEST_running_histories_UNMODIFIED": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "executed_test_sha256": binding.sha(__file__),
        "tested_pure_selection_module_sha256": binding.sha(selection.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "grown_region_pure_selection_controls_completed": True,
        "selected_widest_strict_regions": len(regions), "actual_rejections": len(rejected),
        "verified": False, "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
