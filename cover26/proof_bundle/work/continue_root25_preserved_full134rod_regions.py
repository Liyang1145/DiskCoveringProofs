"""NEW root25 v3 -> full134rod region successor, no old history reset."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_candidate_identity_after_six_target as identity
import n26_checked_full134rod_closed_intersections as intersections
import n26_typed_arithmetic_context as codec
import probe_candidate_positive_curvature_hull as fixed
import probe_full_candidate_face_energy as diagonal
import probe_full134rod_correlated_support as correlated_proposal
import test_checked_root25_support_cost_continuation as seed_tests
import test_full_candidate_face_energy as inverse_tests
import verify_conditional_force_stage as binding


SCHEMA = "N26-unaccepted-root25-v3-preserved-full134rod-region-successor-v1"
mixed = intersections.mixed
RESOURCE = Path("outputs/n26-original-candidate-arithmetic-context-v1")
SOURCE = Path("outputs/n26-current-candidate-owned-forest-v8")
SEED = Path("outputs/n26-candidate-root25-checked-support-cost-forest-diagnosis-v3.json")
SEED_TESTS = Path("outputs/n26-candidate-root25-checked-support-cost-independent-controls-v3.json")
REGION_DATA = Path("outputs/n26-latest-root25-fresh-correlated-stress-v1.json")
REGION_TESTS = Path("outputs/n26-latest-root25-fresh-correlated-independent-arithmetic-v1.json")
CURRENT = Path("outputs/n26-current28-six-target-supplemental-current-v1.json")
FINAL = Path("outputs/n26-current28-six-target-supplemental-independent-final-v1.json")


def modules():
    return (identity, intersections, intersections.cutter, mixed, mixed.old,
            mixed.old.prior, mixed.old.prior.signed, mixed.correlated,
            mixed.correlated.full, codec, diagonal, correlated_proposal,
            seed_tests, seed_tests.producer, inverse_tests)


def inputs():
    paths = (RESOURCE/"VERIFIED.json", RESOURCE/"CONTEXT.json",
             Path("outputs/n26-original-candidate-arithmetic-context-published-replay-v1.json"),
             SOURCE/"VERIFIED.json", SEED, SEED_TESTS, REGION_DATA, REGION_TESTS, CURRENT, FINAL,
             Path("work/n26-root25-preserved-full134rod-region-continuation-proof.md"))
    digests = {linux(path): binding.sha(path) for path in paths}
    resource = binding.read(RESOURCE/"VERIFIED.json")
    if (
        binding.sha(RESOURCE/"VERIFIED.json") != fixed.RESOURCE_SHA
        or binding.read(paths[2]) != resource or binding.sha(paths[2]) != fixed.RESOURCE_SHA
        or resource["context_is_not_a_current_candidate_source_or_a_seed_history_substitute"] is not True
        or resource["resource_acceptance_is_not_a_faster_current_source_interface"] is not True
        or resource["files"]["CONTEXT.json"] != binding.sha(RESOURCE/"CONTEXT.json")
        or resource["files"]["n26_typed_arithmetic_context.py"] != binding.sha(codec.__file__)
    ):
        raise ValueError("root25 full134rod successor changed arithmetic DATA identity/scope")
    typed = codec.gate(binding.read(RESOURCE/"CONTEXT.json")["typed_context"])
    original, original_kernel = typed["original"], typed["original_kernel"]
    seed, controls = binding.read(SEED), binding.read(SEED_TESTS)
    if (
        seed["schema"] != seed_tests.producer.SCHEMA
        or seed["executed_producer_sha256"] != binding.sha(seed_tests.producer.__file__)
        or controls["schema"] != seed_tests.SCHEMA
        or controls["executed_test_sha256"] != binding.sha(seed_tests.__file__)
        or controls["diagnosis_sha256"] != binding.sha(SEED)
        or controls["latest_arithmetic_result"] != seed["arithmetic_result"]
        or controls["both_entire_actual_closed_root_partitions_and_exact_ledgers_reconstructed"] is not True
        or controls["all_previous_non_OPEN_nodes_positive_supports_and_proved_ledgers_preserved_identically"] is not True
        or len(controls["actual_rejection_controls_passed"]) != 20
        or seed["source_OPEN_index"] != 25 or controls["source_OPEN_index"] != 25
        or seed.get("full134rod_supports") or controls["retained_OPEN_leaves"] != 686
    ):
        raise ValueError("root25 successor lacks actual latest independently checked v3 history")
    accepted = binding.read(SOURCE/"VERIFIED.json")
    for name, digest in seed["source_file_sha256"].items():
        path = SOURCE/name
        if binding.sha(path) != digest or accepted["files"][name] != digest:
            raise ValueError("root25 source/root/history DATA changed")
        digests[linux(path)] = digest
    row = next(item for item in binding.read(SOURCE/"PENDING-ANGLES.json") if item["index"] == 25)
    if row != controls["actual_source_closed_box"]:
        raise ValueError("root25 whole source ownership changed")
    current, final = binding.read(CURRENT), binding.read(FINAL)
    current_digest = binding.sha(CURRENT)
    if (
        final["current_audit_sha256"] != current_digest
        or final["all_current_file_digests_rehashed"] is not True
        or final["current_file_digests_rechecked"] != len(current["files"])
        or current_digest != "c85e130c935e68e2275e53fa457c9c4d95d8be5416b128f4307a76061057911b"
        or F(current["r_strict_interval"][1]) != F(original["radius"])
    ):
        raise ValueError("root25 full134rod successor lacks actual completed proof-time SIX pair")
    layer = identity.gate(current, current_digest, SOURCE)
    data, tests = binding.read(REGION_DATA), binding.read(REGION_TESTS)
    if (
        data["source_OPEN_index"] != 25 or tests["source_OPEN_index"] != 25
        or tests["input_sha256"].get(str(REGION_DATA)) != binding.sha(REGION_DATA)
        or tests["strict_whole_parent_leaves"] != 0
        or tests["strict_proper_neighborhoods_NOT_disjoint_payments"] != 6
        or tests["actual_closed_target_certificates_independently_reconstructed"] != 9
        or tests["all_actual_latest_forest_nodes_supports_ledgers_and_payments_UNMODIFIED"] is not True
    ):
        raise ValueError("root25 stress DATA lacks its actual independent closed-region evidence")
    for report in (seed, controls, data, tests):
        if (
            report["verified"] is not False or report["new_geometric_payments"] != 0
            or report["candidate_whole_roots_removed"] != 0
            or report["global_optimality_proved"] is not False
        ):
            raise ValueError("arithmetic DATA was relabelled as geometry/current acceptance")
    for text, digest in tests["input_sha256"].items():
        if binding.sha(text) != digest:
            raise ValueError("root25 independent prior stress arithmetic changed")
    model = mixed.model_gate(original)
    pending = {leaf["index"]: leaf for leaf in seed["pending_closed_leaf_boxes"]}
    if len(pending) != 686:
        raise ValueError("root25 latest pending ownership duplicated/truncated")
    table, kernels, items = [], [], []
    for item in data["results"]:
        leaf = item["actual_latest_root25_v3_OPEN_leaf"]
        if pending.get(leaf["index"]) != leaf or seed["nodes"][leaf["index"]] != {"kind": "OPEN"}:
            raise ValueError("root25 stress origin is not actual latest v3 OPEN")
        trials = [trial for trial in item["trials"] if trial["domain"] == "proper_closed_halfwidth_1/500"]
        if len(trials) != 1 or trials[0]["fresh_correlated_result"]["arithmetic_strict_target_test_passed"] is not True:
            raise ValueError("root25 proper seed region lost its exact strict bound")
        trial = trials[0]
        certificate = item["fresh_full134rod_positive_stress_kernel_certificate"]
        kernel, _ = inverse_tests.kernel_controls(model, certificate)
        table.append({"mode": mixed.SUPPORT_MODE, "kernel_certificate": certificate,
                      "suggestion_point_turns": trial["fresh_correlated_certificate"]["reference_turns"]})
        kernels.append(kernel)
        items.append((leaf, trial))
    if len(table) != 3:
        raise ValueError("root25 continuation changed the actual three stress origins")
    return original, original_kernel, seed, row, table, kernels, items, digests, layer


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--max-targets", type=int, default=128)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("preserve existing root25 successor rather than reset to v3")
    values = inputs()
    original, original_kernel, seed, row, table, kernels, items, digests, layer = values
    module_hashes = {linux(Path(module.__file__)): binding.sha(module.__file__) for module in modules()}
    executed = binding.sha(__file__)
    arcs = binding.force.load_trig(RESOURCE)[0]
    base = mixed.old.prior.prior
    root = base.tighten(original["matrix"], row["sharp_lower"], row["sharp_upper"])
    tight = [axis for axis, (a, b) in enumerate(zip(*root)) if b-a <= F(1, 10**7)]
    regions, trials = [], []
    for support_index, (leaf, old_trial) in enumerate(items):
        kernel = kernels[support_index]
        initial = old_trial["fresh_correlated_certificate"]
        reference = list(map(F, initial["reference_turns"]))
        best = None
        for width in (F(1, 500), F(1, 250), F(1, 125), F(1, 64), F(1, 32), F(1, 16)):
            a = [max(x, r-width) for x, r in zip(root[0], reference)]
            b = [min(y, r+width) for y, r in zip(root[1], reference)]
            box = base.tighten(original["matrix"], a, b)
            if box is None or box != base.independently_contract(original["matrix"], a, b):
                raise ValueError("root25 grown reference neighborhood failed independent contraction")
            certificate, result, failure, strategy = deepcopy(initial), None, None, "retested-original-tangent"
            try:
                result = mixed.correlated.bound(
                    kernel, original["matrix"], *box, certificate, original["radius"], arcs)
            except ValueError as error:
                failure = str(error)
            if result is None or not result["arithmetic_strict_target_test_passed"]:
                diagonal_certificate, _ = diagonal.suggest_bound(
                    original, kernel, box, reference, tight, arcs, 16)
                if diagonal_certificate is not None:
                    shape = {"lower": list(map(str, box[0])), "upper": list(map(str, box[1]))}
                    certificate, result, _ = correlated_proposal.suggest(
                        kernel, original, shape, diagonal_certificate, arcs)
                    strategy = "fresh-exactly-checked-correlated-tangent"
            strict = result is not None and result["arithmetic_strict_target_test_passed"]
            trials.append({
                "support_index": support_index, "origin_actual_v3_OPEN_leaf_index": leaf["index"],
                "requested_closed_half_width": str(width),
                "actual_closed_lower": list(map(str, box[0])),
                "actual_closed_upper": list(map(str, box[1])),
                "certificate": certificate, "exact_result": result,
                "strict_entire_actual_closed_region": strict,
                "strategy": strategy, "original_tangent_rejection_if_any": failure,
            })
            print(json.dumps({"root25_actual_origin_leaf": leaf["index"],
                              "grown_half_width": str(width), "strict_closed_region": strict,
                              "formal_payments": 0}), flush=True)
            if strict:
                best = {"lower": list(map(str, box[0])), "upper": list(map(str, box[1])),
                        "full_support_index": support_index, "certificate": certificate}
            elif best is not None:
                break
        if best is None:
            raise ValueError("root25 continuation lost its actual checked strict initial region")
        regions.append(best)
    def progress(target, count):
        print(json.dumps({"root25_NEW_full134_strict_targets": count,
                          "actual_OPEN_source": target["source_actual_OPEN_leaf"]["index"],
                          "whole_actual_OPEN_leaf": target["whole_source_OPEN_leaf"],
                          "formal_payments": 0}), flush=True)
    nodes, targets, cuts, scans = intersections.refine(
        original, arcs, row, seed["nodes"], kernels, regions, args.max_targets, progress)
    result, pending, ledger = mixed.replay(
        original, original_kernel, arcs, row, nodes, seed["alternative_supports"], table)
    retained = mixed.retention_gate(seed, {
        "nodes": nodes, "alternative_supports": seed["alternative_supports"],
        "full134rod_supports": table, "arithmetic_ledger": ledger})
    for text, digest in {**digests, **module_hashes}.items():
        if binding.sha(text) != digest:
            raise ValueError("root25 continuation input/implementation changed")
    if binding.sha(__file__) != executed:
        raise ValueError("root25 continuation producer changed during execution")
    report = {
        "schema": SCHEMA, "verified": False, "source_OPEN_index": 25,
        "actual_source_closed_box": row, "source_file_sha256": seed["source_file_sha256"],
        "actual_checked_latest_root25_v3_sha256": binding.sha(SEED),
        "actual_checked_latest_root25_v3_controls_sha256": binding.sha(SEED_TESTS),
        "actual_proof_time_current_sha256": binding.sha(CURRENT),
        "actual_candidate_identity_DATA_only": layer,
        "all_input_sha256": digests, "modules": module_hashes,
        "nodes": nodes, "alternative_supports": seed["alternative_supports"],
        "full134rod_supports": table, "arithmetic_result": result,
        "pending_closed_leaf_boxes": pending, "arithmetic_ledger": ledger,
        "old_nodes_supports_and_strict_ledgers_preserved_identically": list(retained),
        "all_fresh_actual_closed_root25_region_trials": trials,
        "selected_widest_actually_strict_closed_regions": regions,
        "fresh_actual_OPEN_intersection_targets": targets,
        "fresh_closed_split_decisions": cuts, "region_scans": scans,
        "old_v3_tree_NOT_reset_and_no_root28_tree_or_payment_imported": True,
        "all_closed_halves_shared_boundaries_and_nonempty_remainders_retained": True,
        "three_full134rod_stresses_are_universal_arithmetic_DATA_ONLY": True,
        "original_52_coordinate_LOCAL_allowance_unchanged": "7/800000",
        "separate_independent_arithmetic_controls_still_required": True,
        "entire_latest_source_model_history_geometry_admission_NOT_performed": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_producer_sha256": executed,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"root25_preserved_full134rod_successor_completed": True,
                      "NEW_strict_targets": len(targets),
                      "whole_old_OPEN_leaves_paid": sum(item["whole_source_OPEN_leaf"] for item in targets),
                      "retained_OPEN_leaves": len(pending),
                      "entire_root_arithmetic_cover_completed": not pending,
                      "formal_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
