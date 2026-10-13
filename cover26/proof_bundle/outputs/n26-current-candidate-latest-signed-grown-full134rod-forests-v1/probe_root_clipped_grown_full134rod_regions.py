"""Fresh larger source-root regions for checked positive full134rod stresses.

Old v7 point/stress records are arithmetic DATA, not the latest forest seed.
No currently running or accepted forest, source history or payment is edited.
"""

import argparse
from argparse import Namespace
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import probe_balanced_full134rod_neighborhoods as inputs
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-actual-source-root-clipped-grown-full134rod-regions-v1"
WIDTHS = (F(1, 1000), F(1, 500), F(1, 200), F(1, 100), F(1, 50))
ARGUMENTS = (
    "resource", "resource-replay", "current-audit", "ancestor-current-audit",
    "source", "seed", "seed-controls", "ancestor-seed", "old-full-diagnosis",
    "old-full-controls", "prior-diagnosis", "prior-controls",
    "correlated-diagnosis", "correlated-controls", "old-minimax-diagnosis",
    "old-minimax-controls", "balanced-diagnosis", "balanced-controls",
)


def arguments(test=False):
    parser = argparse.ArgumentParser()
    for name in (*ARGUMENTS, *(("diagnosis",) if test else ()), "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    return parser.parse_args()


def data_gate(args):
    old_args = Namespace(**vars(args))
    old_args.current_audit = args.ancestor_current_audit
    original, model, old_seed, row, arcs, digests, _, stresses = inputs.data_gate(old_args)
    for name in ARGUMENTS:
        path = getattr(args, name.replace("-", "_"))
        if name in ("resource", "source"):
            path = path / "VERIFIED.json"
        digests[path] = binding.sha(path)
    current, digest = binding.read(args.current_audit), digests[args.current_audit]
    layer = identity.gate(current, digest, args.source)
    if F(original["radius"]) != F(current["r_strict_interval"][1]):
        raise ValueError("grown root regions changed the current same-root radius")
    return original, model, old_seed, row, arcs, digests, layer, stresses


def region_gate(original, row, turns, width):
    if width not in WIDTHS:
        raise ValueError("unknown actual source-root region width")
    base = inputs.stress_producer.old.prior_producer.previous.producer.latest_controls.producer.BASE
    box = base.tighten(
        original["matrix"], [max(F(a), t-width) for a, t in zip(row["sharp_lower"], turns)],
        [min(F(b), t+width) for b, t in zip(row["sharp_upper"], turns)])
    independent = base.independently_contract(
        original["matrix"], [max(F(a), t-width) for a, t in zip(row["sharp_lower"], turns)],
        [min(F(b), t+width) for b, t in zip(row["sharp_upper"], turns)])
    if box is None or box != independent:
        raise ValueError("grown region lost its source-root reference or independent contraction")
    inputs.full.hull.quadratic.reference_gate(turns, *box, original["matrix"])
    return box


def modules():
    return (
        inputs, inputs.full, inputs.stress_producer, inputs.stress_controls,
        inputs.stress_producer.old.prior_producer,
        inputs.stress_producer.old.prior_producer.previous.producer.old_probe,
        identity,
    )


def unchanged(args, digests, seed, module_digests, producer_digest):
    inputs.stress_producer.old.prior_producer.previous.producer.unchanged_inputs(args, digests, seed)
    for path, digest in module_digests.items():
        if binding.sha(binding.local_path(path)) != digest:
            raise ValueError("grown source-root arithmetic module changed during execution")
    if binding.sha(__file__) != producer_digest:
        raise ValueError("grown source-root producer changed during execution")


def main():
    args = arguments()
    if args.report.exists():
        raise FileExistsError(args.report)
    original, model, seed, row, arcs, digests, layer, stresses = data_gate(args)
    producer_digest = binding.sha(__file__)
    module_digests = {linux(Path(module.__file__)): binding.sha(module.__file__) for module in modules()}
    base = inputs.stress_producer.old.prior_producer.previous.producer.latest_controls.producer.BASE
    root_box = base.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root_box)) if b-a <= F(1, 10**7)]
    results = []
    for item in stresses["results"]:
        turns = list(map(F, item["actual_fixed_feasible_anchor_turns"]))
        kernel, kernel_identity = inputs.stress_producer.old.prior_producer.previous.arithmetic.kernel_controls(
            model, item["NEW_full134rod_stress_kernel_certificate"])
        trials = []
        for width in WIDTHS:
            box = region_gate(original, row, turns, width)
            diagonal, diagonal_result = inputs.stress_producer.old.prior_producer.previous.producer.old_probe.suggest_bound(
                original, kernel, box, turns, tight, arcs, 16)
            certificate, result, numeric = None, None, None
            if diagonal is not None:
                certificate, result, numeric = inputs.stress_producer.old.prior_producer.suggest(
                    kernel, original, {"lower": list(map(str, box[0])), "upper": list(map(str, box[1]))},
                    diagonal, arcs)
            strict = result is not None and result["arithmetic_strict_target_test_passed"]
            whole = box == root_box
            trials.append({
                "requested_root_closed_half_width": str(width),
                "actual_source_root_clipped_closed_lower": list(map(str, box[0])),
                "actual_source_root_clipped_closed_upper": list(map(str, box[1])),
                "region_equals_entire_actual_source_root": whole,
                "old_checked_v7_leaf_boundary_NOT_used_to_clip_this_region": True,
                "NEW_diagonal_certificate": diagonal,
                "NEW_diagonal_result": diagonal_result,
                "NEW_correlated_certificate": certificate,
                "NEW_correlated_result": result,
                "fresh_exact_strict_closed_region": strict,
                "numerical_suggestions_NOT_proofs": numeric,
            })
            print(json.dumps({
                "stress_data_old_reference_leaf": item["actual_checked_v7_OPEN_leaf"]["index"],
                "root_clipped_width": str(width), "fresh_exact_strict_region": strict,
                "region_equals_whole_source_root": whole,
                "verified": False, "new_geometric_payments": 0,
            }), flush=True)
        results.append({
            "checked_old_v7_point_origin_DATA_only": item["actual_checked_v7_OPEN_leaf"],
            "actual_feasible_reference_turns": list(map(str, turns)),
            "NEW_full134rod_stress_kernel_certificate": item["NEW_full134rod_stress_kernel_certificate"],
            "fresh_NEW_full134rod_kernel_identity": kernel_identity,
            "trials": trials,
        })
    unchanged(args, digests, seed, module_digests, producer_digest)
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": row["index"],
        "actual_source_closed_box": row, "source_file_sha256": seed["source_file_sha256"],
        "actual_supplied_current_audit_sha256": digests[args.current_audit],
        "actual_latest_candidate_layer_identity_only": layer,
        "explicit_OLD_v7_stress_origin_forest_sha256": digests[args.seed],
        "balanced_stress_diagnosis_sha256": digests[args.balanced_diagnosis],
        "balanced_stress_controls_sha256": digests[args.balanced_controls],
        "NEW_distinct_full134rod_edges": model["edges"],
        "checked_root_half_widths": list(map(str, WIDTHS)), "results": results,
        "nested_regions_are_NOT_disjoint_paid_leaves_or_a_latest_forest_cover": True,
        "all_original_and_NEWEST_running_forests_supports_and_ledgers_UNMODIFIED": True,
        "successful_regions_NEED_fresh_latest_OPEN_intersections_and_all_remainders": True,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
        "independent_region_arithmetic_controls_still_required": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False, "executed_probe_sha256": producer_digest, "modules": module_digests,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_source_root_grown_full134rod_regions_completed": True,
        "actual_regions": sum(len(item["trials"]) for item in results),
        "strict_regions": sum(trial["fresh_exact_strict_closed_region"]
                              for item in results for trial in item["trials"]),
        "verified": False, "new_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
