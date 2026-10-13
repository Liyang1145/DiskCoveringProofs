"""Actual newest descendant ownership plus independent NEW134rod arithmetic."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import probe_newest_full134rod_robust_descendants as producer
import test_full_candidate_face_energy as arithmetic
import verify_conditional_force_stage as binding


SCHEMA = "N26-independent-actual-newest-full134rod-descendant-arithmetic-controls-v1"


def scope_gate(record, seed, ancestor_seed, model, args, digests):
    if (record["schema"] != producer.SCHEMA
            or record["executed_probe_sha256"] != binding.sha(producer.__file__)
            or record["checked_newest_forest_sha256"] != digests[args.seed]
            or record["checked_newest_forest_controls_sha256"] != digests[args.seed_controls]
            or record["retained_ancestor_forest_sha256"] != digests[args.ancestor_seed]
            or record["checked_old_full134rod_diagnosis_sha256"] != digests[args.old_full_diagnosis]
            or record["checked_old_full134rod_controls_sha256"] != digests[args.old_full_controls]
            or record["actual_current_audit_sha256"] != digests[args.current_audit]
            or record["source_OPEN_index"] != seed["source_OPEN_index"]
            or record["actual_source_closed_box"] != seed["actual_source_closed_box"]
            or record["source_file_sha256"] != seed["source_file_sha256"]
            or record["NEW_distinct_full134rod_edges"] != model["edges"]
            or record["verified"] is not False
            or record["new_geometric_payments"] != 0 or record["candidate_whole_roots_removed"] != 0
            or record["whole_actual_root_cover_NOT_proved"] is not True
            or record["complete_latest_source_model_history_geometry_admission_NOT_performed"] is not True
            or record["all_newest_nodes_supports_nonOPEN_proofs_and_ledgers_UNMODIFIED"] is not True
            or record["only_actual_contained_newest_OPEN_descendants_freshly_tested"] is not True
            or record["universal_checked_positive_kernels_reused_as_DATA_NOT_old_leaf_bound_payments"] is not True):
        raise ValueError("newest fullface supplemental diagnostic changed actual scope/lineage")
    for module in (producer.full, producer.codec, producer.identity, producer.old_probe,
                   arithmetic, producer.latest_controls, producer.dual_suggestion):
        if record["modules"][linux(Path(module.__file__))] != binding.sha(module.__file__):
            raise ValueError("newest fullface actual executed module changed")
    # Independent parent walk, rather than the producer's ancestor DFS.
    parents = {}
    for index, node in enumerate(seed["nodes"]):
        if node["kind"] == "SPLIT":
            for child in node["children"]:
                if child in parents:
                    raise ValueError("newest actual closed tree has a multiply-owned child")
                parents[child] = index
    old = {leaf["index"]: leaf for leaf in ancestor_seed["pending_closed_leaf_boxes"]}
    newest = {leaf["index"]: leaf for leaf in seed["pending_closed_leaf_boxes"]}
    seen = set()
    if not isinstance(record["results"], list) or not 1 <= len(record["results"]) <= 4:
        raise ValueError("newest fullface diagnostic has no actual newest leaf")
    for item in record["results"]:
        leaf, ancestor = item["actual_newest_OPEN_leaf"], item["retained_old_OPEN_ancestor"]
        index, ancestor_index = leaf["index"], ancestor["index"]
        if (type(index) is not int or index in seen
                or index not in newest or newest[index] != leaf
                or seed["nodes"][index] != {"kind": "OPEN"}
                or ancestor_index not in old or old[ancestor_index] != ancestor
                or ancestor_seed["nodes"][ancestor_index] != {"kind": "OPEN"}):
            raise ValueError("newest fullface supplement changed, repeated or reused a nonOPEN leaf")
        seen.add(index)
        cursor, ancestors = index, set()
        while cursor != ancestor_index:
            if cursor in ancestors or cursor not in parents:
                raise ValueError("newest fullface actual leaf has a different retained ancestor")
            ancestors.add(cursor)
            cursor = parents[cursor]
        if any(not F(a) <= F(c) <= F(d) <= F(b) for a, b, c, d in zip(
                ancestor["lower"], ancestor["upper"], leaf["lower"], leaf["upper"])):
            raise ValueError("newest fullface exact descendant containment failed")
        if not isinstance(item["trials"], list) or not item["trials"]:
            raise ValueError("actual newest leaf has no reconstructed fullface trial")
    return len(seen)


def scope_rejections(record, seed, ancestor, model, args, digests):
    rejected = []
    for label, mutation in (
        ("newest-fullface-old-forest-digest-substituted", lambda bad: bad.update(
            checked_newest_forest_sha256=digests[args.ancestor_seed])),
        ("newest-fullface-closed-node-reused-as-OPEN", lambda bad:
            bad["results"][0]["actual_newest_OPEN_leaf"].update(index=1132)),
        ("newest-fullface-actual-leaf-box-changed", lambda bad:
            bad["results"][0]["actual_newest_OPEN_leaf"]["upper"].__setitem__(0, "100")),
        ("newest-fullface-ancestor-ownership-invented", lambda bad:
            bad["results"][0]["retained_old_OPEN_ancestor"].update(index=-1)),
        ("newest-fullface-old-ancestor-box-changed", lambda bad:
            bad["results"][0]["retained_old_OPEN_ancestor"]["lower"].__setitem__(0, "-100")),
        ("newest-fullface-whole-root-ownership-changed", lambda bad: bad.update(source_OPEN_index=-1)),
        ("newest-fullface-arithmetic-promoted-to-geometry", lambda bad: bad.update(
            verified=True, new_geometric_payments=1)),
        ("newest-fullface-own-executor-spoofed", lambda bad: bad.update(
            executed_probe_sha256="0"*64)),
    ):
        bad = deepcopy(record)
        mutation(bad)
        try:
            scope_gate(bad, seed, ancestor, model, args, digests)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid actual newest fullface scope accepted: "+label)
    return rejected


def main():
    parser = argparse.ArgumentParser()
    for name in ("resource", "resource-replay", "current-audit", "source", "seed",
                 "seed-controls", "ancestor-seed", "old-full-diagnosis",
                 "old-full-controls", "diagnosis", "report"):
        parser.add_argument("--"+name, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    original, model, seed, ancestor, old, row, arcs, digests, layer = producer.data_gate(args)
    record, diagnosis_digest = binding.read(args.diagnosis), binding.sha(args.diagnosis)
    actual_leaves = scope_gate(record, seed, ancestor, model, args, digests)
    if record["actual_latest_candidate_layer_identity_only"] != layer:
        raise ValueError("actual newest fullface supplement changed candidate layer identity")
    checked, kernels = [], []
    for item in record["results"]:
        leaf = item["actual_newest_OPEN_leaf"]
        for trial in item["trials"]:
            kernel, exact_identity = arithmetic.kernel_controls(
                model, trial["NEW_full134rod_kernel_certificate"])
            if exact_identity != trial["NEW_full134rod_exact_identity_controls"]:
                raise ValueError("newest fullface nonharmonic square completion changed")
            point = list(map(F, trial["actual_midpoint_turns"]))
            if point != [(F(a)+F(b))/2 for a, b in zip(leaf["lower"], leaf["upper"])]:
                raise ValueError("newest fullface midpoint is not the actual latest leaf midpoint")
            energy = producer.full.hull.quadratic.point_energy_gradient(kernel, [F(0), *point], arcs)[0]
            cap = F(original["radius"])**2*F(sum(kernel["weights"]), kernel["scale"])
            if (str(energy) != trial["exact_midpoint_energy_lower"]
                    or str(cap) != trial["NEW_full134rod_same_root_energy_upper"]
                    or str(energy-cap) != trial["exact_midpoint_strict_energy_margin"]):
                raise ValueError("newest fullface exact point energy or NEWweight sum changed")
            certificate = trial["NEW_full134rod_energy_certificate"]
            if certificate is not None:
                result = arithmetic.bound_controls(original, kernel, leaf, trial, arcs)
                if (trial["strict_actual_newest_closed_leaf_exclusion"] !=
                        result["arithmetic_strict_target_test_passed"]
                        or trial["fresh_reference_turns"] != certificate["reference_turns"]):
                    raise ValueError("newest fullface actual closed leaf/reference claim changed")
                checked.append({"newest_OPEN_leaf": leaf["index"],
                                "retained_old_ancestor": item["retained_old_OPEN_ancestor"]["index"],
                                "strategy": trial["strategy"],
                                "strict_whole_closed_leaf": result["arithmetic_strict_target_test_passed"],
                                "strict_radius_margin": result["strict_radius_margin"],
                                "actual_nonnegative_difference_dual_terms":
                                    result["nonnegative_difference_dual_terms"]})
            elif (trial["NEW_full134rod_exact_closed_leaf_result"] is not None
                  or trial["strict_actual_newest_closed_leaf_exclusion"] is not False):
                raise ValueError("uncertified newest fullface suggestion was declared a strict proof")
            tiny = original["cap"]["known_candidate_tiny_angle_cells"]
            tiny_result = producer.full.direct.bound(
                [a for a, _ in tiny], [b for _, b in tiny], kernel, F(original["radius"])**2, arcs)
            if (tiny_result != trial["known_feasible_tiny_original_same_root_control"]
                    or tiny_result["radius_conditional_whole_angle_box_excluded"]):
                raise ValueError("newest fullface known-feasible tiny positive control failed")
            kernels.append(kernel)
    first = next((item, trial) for item in record["results"] for trial in item["trials"]
                 if trial["NEW_full134rod_energy_certificate"] is not None)
    mode_rejections = arithmetic.rejection_controls(
        original, model, first[0]["actual_newest_OPEN_leaf"], first[1], arcs)
    newest_rejections = scope_rejections(record, seed, ancestor, model, args, digests)
    if len(mode_rejections) != 20 or len(newest_rejections) != 8:
        raise AssertionError("newest fullface tester omitted a required actual rejection")
    producer.unchanged_inputs(args, digests, seed)
    if binding.sha(args.diagnosis) != diagnosis_digest:
        raise ValueError("newest fullface actual diagnostic changed during independent controls")
    report = {
        "schema": SCHEMA, "verified": False, "diagnosis_sha256": diagnosis_digest,
        "checked_newest_forest_sha256": digests[args.seed],
        "checked_newest_forest_controls_sha256": digests[args.seed_controls],
        "retained_ancestor_forest_sha256": digests[args.ancestor_seed],
        "actual_entire_newest_old_mode_forest_and_all_ledgers_reconstructed": True,
        "independent_parent_walk_and_exact_actual_OPEN_descendant_containment_checked": actual_leaves,
        "actual_NEW60ground_incidence_inverse_harmonic_Schur_identities_checked": len(kernels),
        "actual_newest_full134rod_closed_leaf_results_independently_reconstructed": checked,
        "independent_sine_square_feasible_corner_midpoint_checks": 3*len(checked),
        "known_feasible_tiny_NEW134rod_positive_controls_passed": len(kernels),
        "actual_NEW134rod_mode_rejection_controls_passed": mode_rejections,
        "actual_newest_descendant_scope_rejection_controls_passed": newest_rejections,
        "all_newest_nodes_supports_nonOPEN_proofs_and_ledgers_UNMODIFIED": True,
        "universal_checked_positive_kernels_reused_as_DATA_NOT_old_leaf_bound_payments": True,
        "arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance": True,
        "whole_actual_root_cover_NOT_proved": True,
        "source_file_sha256": seed["source_file_sha256"],
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False, "executed_test_sha256": binding.sha(__file__),
        "tested_NEW_full134rod_module_sha256": binding.sha(producer.full.__file__),
        "tested_newest_probe_sha256": binding.sha(producer.__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"actual_newest_full134rod_independent_controls_completed": True,
                      "actual_newest_OPEN_leaves": actual_leaves,
                      "exact_whole_closed_leaf_trials": len(checked),
                      "strict_newest_closed_leaf_trials": sum(
                          trial["strict_whole_closed_leaf"] for trial in checked),
                      "actual_rejections": len(mode_rejections)+len(newest_rejections),
                      "verified": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
