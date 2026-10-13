"""Distinct own-executor product mode over a fully admitted mixed source.

No typed diagnostic context is imported. All original geometry/model,
accepted mixed modes, old payments and latest histories are replayed afresh.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_mixed_curvature_candidate_source as source
import n26_product_forest_acceptance_controls as product_controls
import verify_conditional_force_stage as binding
import verify_current_candidate_mixed_curvature_covers as prior


INPUT_SCHEMA = "N26-current-product-Taylor-LOCAL-forest-bindings-v1"
SCHEMA = "N26-accepted-current-product-Taylor-LOCAL-forests-v1"
CHECKER = "verify_current_candidate_product_forests.py"
MODE = "difference-product-Taylor"
DIAGNOSIS = "N26-unaccepted-continued-root-difference-product-LOCAL-forest-diagnosis-v1"
ARITHMETIC = "N26-independent-actual-product-forest-arithmetic-controls-v1"
GUARD = "N26-product-forest-own-executor-interface-guard-controls-v1"


def executed_modules():
    forest = product_controls.forest
    return (*prior.executed_modules(), source, source.identity, product_controls,
            forest, forest.product)


def continuation_gate(seed, diagnosis):
    if (diagnosis["schema"] != DIAGNOSIS or diagnosis["verified"] is not False
            or diagnosis["new_geometric_payments"] != 0
            or diagnosis["candidate_whole_roots_removed"] != 0
            or diagnosis["complete_latest_model_source_ownership_replay_NOT_performed"] is not True
            or diagnosis["new_product_mode_NOT_admitted_by_running_mixed_checker"] is not True
            or diagnosis["all_previous_non_OPEN_nodes_preserved_identically"] is not True
            or seed["verified"] is not False or seed["new_geometric_payments"] != 0
            or seed["candidate_whole_roots_removed"] != 0
            or seed["actual_source_closed_box"] != diagnosis["actual_source_closed_box"]
            or seed["source_OPEN_index"] != diagnosis["source_OPEN_index"]
            or len(diagnosis["nodes"]) < len(seed["nodes"])
            or any(old["kind"] != "OPEN" and diagnosis["nodes"][index] != old
                   for index, old in enumerate(seed["nodes"]))):
        raise ValueError("product continuation changed ownership, zero-payment scope or old closed nodes")


def proposed_forests(seed, diagnosis):
    continuation_gate(seed, diagnosis)
    return [{
        "mode": MODE, "source_OPEN_index": diagnosis["source_OPEN_index"],
        "actual_source_closed_box": diagnosis["actual_source_closed_box"],
        "nodes": diagnosis["nodes"],
    }]


def root_gate(incoming, proposed):
    by_index = prior.constant.root_gate(incoming, proposed)
    if any(set(item) != {"mode", "source_OPEN_index", "actual_source_closed_box", "nodes"}
           or item["mode"] != MODE for item in proposed):
        raise ValueError("product forest lost its explicit distinct mode or added proof fields")
    return by_index


def metadata_gate(folder):
    manifest = binding.read(folder / "MANIFEST.json")
    if (manifest["schema"] != INPUT_SCHEMA or manifest["radius_scope"] != "same-root-Rstar"
            or manifest["acceptance_checker_file"] != CHECKER
            or manifest["supported_curvature_modes"] != [MODE]
            or manifest["required_source_schema"] != prior.SCHEMA
            or manifest["typed_resource_not_a_source_replay_substitute"] is not True
            or manifest["supplemental_forest_never_resets_accepted_history"] is not True):
        raise ValueError("product interface changed its own executor, source schema or admission scope")
    for name, digest in manifest["copied_files"].items():
        if binding.sha(folder / name) != digest:
            raise ValueError("product sealed input changed: " + name)
    for module in executed_modules():
        if binding.sha(module.__file__) != manifest["copied_files"][Path(module.__file__).name]:
            raise ValueError("product executor uses different sealed source/model/arithmetic modules")
    if (Path(__file__).name != CHECKER
            or binding.sha(__file__) != manifest["copied_files"][CHECKER]):
        raise ValueError("product interface does not bind its actual own executor")
    seed = binding.read(folder / "OLD-ARITHMETIC-FOREST.json")
    diagnosis = binding.read(folder / "DIAGNOSIS.json")
    continuation_gate(seed, diagnosis)
    if diagnosis["old_unadmitted_forest_sha256"] != binding.sha(folder / "OLD-ARITHMETIC-FOREST.json"):
        raise ValueError("product interface lost actual old diagnostic lineage")
    arithmetic = binding.read(folder / "ARITHMETIC-CONTROLS.json")
    if (arithmetic["schema"] != ARITHMETIC
            or arithmetic["verified"] is not False
            or arithmetic["new_geometric_payments"] != 0
            or arithmetic["candidate_whole_roots_removed"] != 0
            or arithmetic["actual_entire_closed_root_arithmetic_reconstruction_passed"] is not True
            or arithmetic["arithmetic_only_NOT_complete_latest_model_source_history_or_geometry_acceptance"]
            is not True
            or arithmetic["diagnosis_sha256"] != binding.sha(folder / "DIAGNOSIS.json")
            or arithmetic["old_forest_sha256"] != binding.sha(folder / "OLD-ARITHMETIC-FOREST.json")
            or len(arithmetic["rejection_controls_passed"]) != 13
            or arithmetic["executed_test_sha256"] != manifest["copied_files"][
                "test_candidate_difference_product_forest_arithmetic.py"]):
        raise ValueError("product interface lacks actual independent whole-root arithmetic controls")
    for name in ("n26_difference_product_candidate_forest.py",
                 "n26_difference_product_curvature.py", "n26_candidate_energy_local_forest.py"):
        if arithmetic["tested_modules"][name] != manifest["copied_files"][name]:
            raise ValueError("product arithmetic controls tested different geometry arithmetic")
    guard = binding.read(folder / "INTERFACE-GUARD-CONTROLS.json")
    if (guard["schema"] != GUARD
            or guard["metadata_guard_controls_passed"] is not True
            or guard["verified"] is not False or guard["new_geometric_payments"] != 0
            or guard["candidate_whole_roots_removed"] != 0
            or guard["complete_latest_source_model_history_gate_NOT_executed"] is not True
            or guard["tested_own_executor_sha256"] != binding.sha(__file__)
            or guard["tested_pure_controls_sha256"] != binding.sha(product_controls.__file__)
            or guard["executed_test_sha256"] != manifest["copied_files"][
                "test_product_forest_own_executor_interface.py"]
            or len(guard["actual_arithmetic_rejection_paths_exercised"]) != 13
            or len(guard["actual_ownership_history_and_mode_rejection_paths_exercised"]) != 6):
        raise ValueError("product interface lacks actual distinct-mode own-executor guards")
    return manifest, seed, diagnosis


def input_gate(folder):
    manifest, seed, diagnosis = metadata_gate(folder)
    source_folder = binding.local_path(manifest["source"])
    replay_path = binding.local_path(manifest["source_replay"])
    parent_path = binding.local_path(manifest["parent_current_audit"])
    rehash_path = binding.local_path(manifest["parent_digest_recheck"])
    parent, rehash = binding.read(parent_path), binding.read(rehash_path)
    if (binding.sha(parent_path) != manifest["parent_current_audit_sha256"]
            or binding.sha(rehash_path) != manifest["parent_digest_recheck_sha256"]
            or binding.read(folder / "SOURCE-CURRENT-AUDIT.json") != parent
            or binding.read(folder / "SOURCE-FINAL-DIGEST-RECHECK.json") != rehash):
        raise ValueError("product interface changed its completed actual mixed-source parent/final")
    print("Replaying COMPLETE mixed source, original model, all old modes/payments and history.",
          flush=True)
    accepted, values, incoming, inventory, old_payments, history, layer = source.gate(
        source_folder, replay_path, parent_path, rehash_path)
    if (accepted["schema"] != prior.SCHEMA
            or binding.sha(source_folder / "VERIFIED.json") != manifest["source_acceptance_sha256"]
            or binding.read(folder / "SOURCE-ACCEPTANCE.json") != accepted
            or binding.read(folder / "SOURCE-PENDING-ANGLES.json") != incoming
            or len(incoming) != parent["candidate_angle_unresolved_closed_boxes"]
            or F(values[3]["radius"]) != F(parent["r_strict_interval"][1])):
        raise ValueError("product interface changed actual latest mixed ownership, model or radius")
    prior.constant.history_gate(binding.read(folder / "SOURCE-ROOT-HISTORY.json"), history)
    proposed = binding.read(folder / "FORESTS.json")
    if proposed != proposed_forests(seed, diagnosis):
        raise ValueError("product interface changed actual continued certificate DATA")
    root_gate(incoming, proposed)
    inventory.extend((parent_path, rehash_path, replay_path))
    return (manifest, parent, accepted, values, incoming, proposed,
            history, inventory, old_payments, layer)


def derive(values, override=None):
    _, _, _, original_values, incoming, proposed, history, _, _, _ = values
    proposed = proposed if override is None else override
    by_index = root_gate(incoming, proposed)
    original, kernel, arcs = original_values[3], original_values[5], original_values[6]
    payments, classified, ledgers = [], [], []
    for item in proposed:
        index = item["source_OPEN_index"]
        result, pending, ledger = product_controls.forest.replay(
            original, kernel, arcs, by_index[index], item["nodes"])
        if (pending or result["retained_OPEN_leaves"]
                or not result["arithmetic_entire_root_lower_bound_cover_completed"]
                or result["counts"]["LOCAL"] != 1
                or result["arithmetic_entire_root_strictly_empty"]):
            raise ValueError("product supplemental forest did not close its entire energy/LOCAL root")
        payments.append({
            "source_OPEN_index": index, "actual_source_closed_box": by_index[index],
            "source_candidate_root_fully_lower_bounded": True,
            "source_candidate_root_strictly_empty": False,
            "original_LOCAL_equality_region_preserved": True, "mode": MODE,
            "supplemental_closed_forest_result": result,
            "latest_accepted_forest_kept_as_unchanged_prior_proof": history.get(index),
        })
        classified.append({"source_OPEN_index": index, "mode": MODE, **result})
        ledgers.append({"source_OPEN_index": index, "exact_closed_leaf_ledger": ledger})
        print(json.dumps({"actual_product_root_replayed": index,
                          "strict_energy_leaves": result["counts"]["PRODUCT-ENERGY"],
                          "original_LOCAL_leaves": result["counts"]["LOCAL"]}), flush=True)
    discharged = {item["source_OPEN_index"] for item in payments}
    remaining = [row for row in incoming if row["index"] not in discharged]
    retained = [history[index] for index in sorted(history) if index not in discharged]
    if len(payments) + len(remaining) != len(incoming):
        raise ValueError("product forest lost exact whole-root conservation")
    return payments, remaining, classified, ledgers, retained


def ownership_controls(incoming, proposed, history):
    negative = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(label)
        else:
            raise AssertionError("invalid product source ownership/mode control accepted: " + label)

    def changed_roots(mutation):
        bad = deepcopy(proposed)
        mutation(bad)
        root_gate(incoming, bad)

    reject("duplicate-product-whole-root", lambda: changed_roots(
        lambda bad: bad.append(deepcopy(bad[0]))))
    reject("already-paid-root-reopened-by-product", lambda: changed_roots(
        lambda bad: bad[0].update(source_OPEN_index=1794)))
    reject("whole-product-root-domain-clipped", lambda: changed_roots(
        lambda bad: bad[0]["actual_source_closed_box"]["sharp_lower"].__setitem__(0, "0")))
    reject("product-relabelled-as-running-integral-mode", lambda: changed_roots(
        lambda bad: bad[0].update(mode="integrated-Taylor")))
    reject("product-unknown-proof-fields", lambda: changed_roots(
        lambda bad: bad[0].update(arithmetic_result_is_acceptance=True)))
    if not history:
        raise ValueError("product interface requires the actual retained newest partial history")
    bad_history = [deepcopy(history[index]) for index in sorted(history)]
    bad_history[0]["nodes"] = [{"kind": "OPEN"}]
    reject("product-reset-latest-accepted-partial-history", lambda:
           prior.constant.history_gate(bad_history, history))
    return negative


def controls(values):
    _, _, _, original_values, incoming, proposed, history, _, _, _ = values
    by_index = root_gate(incoming, proposed)
    original, kernel, arcs = original_values[3], original_values[5], original_values[6]
    if len(proposed) != 1:
        raise ValueError("this tested product interface requires one explicit continued root")
    first = proposed[0]
    negative, positive = product_controls.controls(
        original, kernel, arcs, by_index[first["source_OPEN_index"]], first["nodes"])
    negative.extend(ownership_controls(incoming, proposed, history))
    if len(negative) != 19:
        raise ValueError("product acceptance omitted an actual arithmetic or source control")
    return {
        "original_full_source_positive_controls":
            prior.constant.prior_checker.base.source.tiny_control(original_values),
        "actual_product_arithmetic_positive_controls": positive,
    }, negative


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    values = input_gate(folder)
    manifest, parent, _, original_values, incoming, _, history, inventory, _, layer = values
    payments, remaining, classified, ledgers, retained = derive(values)
    positive, negative = controls(values)
    certificate = {
        "schema": "N26-accepted-product-Taylor-LOCAL-root-certificate-v1",
        "radius_scope": "same-root-Rstar", "radius_upper": str(original_values[3]["radius"]),
        "accepted_curvature_modes": [MODE],
        "discharged_actual_source_root_indices": [item["source_OPEN_index"] for item in payments],
        "all_uncovered_roots_and_latest_partial_histories_retained": True,
        "supplemental_forest_never_resets_accepted_history": True,
        "LOCAL_lower_bound_is_not_an_emptiness_claim": True,
    }
    outputs = {
        "CERTIFICATE.json": certificate, "ROOT-PAYMENTS.json": payments,
        "PENDING-ANGLES.json": remaining, "ROOT-CLASSIFICATION.json": classified,
        "LOWER-LEDGER.json": ledgers, "REMAINING-ROOT-HISTORY.json": retained,
        "POSITIVE-CONTROLS.json": positive,
    }
    for name, data in outputs.items():
        binding.area.base.publish_or_match(folder / name, data)
    inventory.extend(folder / name for name in manifest["copied_files"])
    digests = {linux(Path(path)): binding.sha(path) for path in inventory}
    report = {
        "schema": SCHEMA, "verified": True, "radius_scope": "same-root-Rstar",
        "radius_upper": str(original_values[3]["radius"]),
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "parent_current_audit_sha256": manifest["parent_current_audit_sha256"],
        "actual_latest_candidate_layer_identity": layer,
        "source_actual_remaining_candidate_roots": len(incoming),
        "new_whole_candidate_source_roots_lower_bounded": len(payments),
        "new_strictly_empty_source_roots": 0,
        "new_source_roots_discharged_with_original_LOCAL": len(payments),
        "unresolved_closed_angle_boxes": len(remaining),
        "accepted_curvature_modes": [MODE],
        "supplemental_strict_product_energy_leaves": sum(
            row["counts"]["PRODUCT-ENERGY"] for row in classified),
        "supplemental_original_LOCAL_leaves": sum(row["counts"]["LOCAL"] for row in classified),
        "new_exact_closed_leaf_payments_in_the_old_owned_forest": 0,
        "original_full_latest_model_source_all_old_payments_and_history_replayed": True,
        "actual_newest_per_root_owned_forests_retained_identically": True,
        "remaining_root_partial_histories_retained": len(retained),
        "all_uncovered_whole_roots_retained_identically": True,
        "original_92_rods_62_vertices_52_coordinate_frame_preserved": True,
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "LOCAL_equality_feasible_regions_never_declared_empty": True,
        "current_global_combinatorial_frontier_nodes_removed": 0,
        "candidate_transport_global_lower_bound_proved": not remaining,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "negative_controls_rejected": negative, "retained_prior_history_entries": len(history),
        "files": {name: binding.sha(folder / name) for name in dict.fromkeys(
            ["MANIFEST.json", *manifest["copied_files"], *outputs])},
        "source_files": digests, "executed_checker_file": CHECKER,
        "executed_checker_sha256": binding.sha(__file__),
    }
    for text, digest in digests.items():
        if binding.sha(text) != digest:
            raise ValueError("product original model/source/history changed during final binding")
    for text, digest in parent["files"].items():
        if binding.sha(text) != digest:
            raise ValueError("product completed current dependency changed during final binding")
    if binding.sha(binding.local_path(manifest["parent_current_audit"])) != manifest[
            "parent_current_audit_sha256"]:
        raise ValueError("product proof-time current snapshot changed")
    with report_path.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("files", "source_files")}, indent=2), flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    verify(args.input, args.report)


if __name__ == "__main__":
    main()
