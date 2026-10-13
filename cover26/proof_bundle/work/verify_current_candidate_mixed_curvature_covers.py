"""Own-executor acceptance of constant-hull and integrated-Taylor root covers.

The complete original owned source/model/history gate is executed afresh.
Both curvature modes run their actual controls. Older sealed verifiers and
accepted per-root forests remain unchanged.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_integrated_hull_local_cover as integral
import verify_conditional_force_stage as binding
import verify_current_candidate_signed_hull_covers as constant
import verify_selected_type_trees as independent


INPUT_SCHEMA = "N26-current-mixed-curvature-LOCAL-root-cover-bindings-v1"
SCHEMA = "N26-accepted-current-mixed-curvature-LOCAL-root-covers-v1"
CHECKER = "verify_current_candidate_mixed_curvature_covers.py"
MODES = ["constant-hull", "integrated-Taylor"]
INTEGRAL_DIAGNOSIS = "N26-unaccepted-integrated-Taylor-hull-original-LOCAL-cover-diagnosis-v1"


def executed_modules():
    return (
        constant, constant.identity, constant.owned, constant.prior_checker,
        constant.covers, constant.covers.hull, constant.covers.hull.quadratic,
        constant.covers.forest, integral, integral.integrated, independent, binding,
    )


def selected_covers(constant_diagnosis, integral_diagnosis):
    result = []
    for mode, diagnosis in zip(MODES, (constant_diagnosis, integral_diagnosis)):
        for item in diagnosis["roots"]:
            if item["all_arithmetic_cover_obligations_passed"]:
                result.append({
                    "mode": mode, "source_OPEN_index": item["source_OPEN_index"],
                    "actual_source_closed_box": item["actual_source_closed_box"],
                    "cover": item,
                })
    return result


def modes_gate(roots):
    if not isinstance(roots, list) or not roots:
        raise ValueError("mixed-curvature acceptance has no explicit root covers")
    present = set()
    for item in roots:
        if (set(item) != {"mode", "source_OPEN_index", "actual_source_closed_box", "cover"}
                or item["mode"] not in MODES
                or item["cover"]["source_OPEN_index"] != item["source_OPEN_index"]
                or item["cover"]["actual_source_closed_box"] != item["actual_source_closed_box"]):
            raise ValueError("mixed cover lost explicit mode or exact root ownership")
        present.add(item["mode"])
    if present != set(MODES):
        raise ValueError("this mixed interface requires both explicitly supported curvature modes")


def metadata_gate(folder):
    manifest = binding.read(folder / "MANIFEST.json")
    if (manifest["schema"] != INPUT_SCHEMA
            or manifest["radius_scope"] != "same-root-Rstar"
            or manifest["acceptance_checker_file"] != CHECKER
            or manifest["supported_curvature_modes"] != MODES
            or manifest["typed_resource_not_a_source_replay_substitute"] is not True
            or manifest["supplemental_cover_never_replaces_accepted_forest"] is not True):
        raise ValueError("mixed curvature changed executor, supported modes or source scope")
    for name, digest in manifest["copied_files"].items():
        if binding.sha(folder / name) != digest:
            raise ValueError("mixed-curvature sealed input changed: " + name)
    for module in executed_modules():
        if binding.sha(module.__file__) != manifest["copied_files"][Path(module.__file__).name]:
            raise ValueError("mixed curvature executes different sealed source/geometry arithmetic")
    if (Path(__file__).name != CHECKER
            or binding.sha(__file__) != manifest["copied_files"][CHECKER]):
        raise ValueError("mixed-curvature acceptance did not bind its actual own executor")
    first = binding.read(folder / "CONSTANT-DIAGNOSIS.json")
    second = binding.read(folder / "INTEGRAL-DIAGNOSIS.json")
    if (first["schema"] not in constant.DIAGNOSES
            or second["schema"] != INTEGRAL_DIAGNOSIS
            or any(row["verified"] is not False or row["new_geometric_payments"] != 0
                   for row in (first, second))
            or first["current_candidate_whole_roots_removed"] != 0
            or second["candidate_whole_roots_removed"] != 0):
        raise ValueError("mixed interface promoted diagnostic covers to geometry acceptance")
    for name, diagnosis_name, test_name, expected_rejections, expected_schema, module_names in (
        ("CONSTANT-ARITHMETIC-CONTROLS.json", "CONSTANT-DIAGNOSIS.json",
         "test_signed_hull_local_cover_arithmetic.py", 11,
         "N26-independent-signed-hull-LOCAL-cover-arithmetic-controls-v1",
         ("n26_signed_hull_local_cover.py", "n26_signed_hull_energy_minorant.py")),
        ("INTEGRAL-ARITHMETIC-CONTROLS.json", "INTEGRAL-DIAGNOSIS.json",
         "test_integrated_hull_cover_arithmetic.py", 12,
         "N26-independent-integrated-hull-LOCAL-arithmetic-controls-v1",
         ("n26_integrated_hull_curvature.py", "n26_signed_hull_energy_minorant.py")),
    ):
        row = binding.read(folder / name)
        if (row["schema"] != expected_schema
                or row["all_arithmetic_cover_reconstructions_passed"] is not True
                or row["new_geometric_payments"] != 0
                or row["candidate_whole_roots_removed"] != 0
                or row["diagnosis_sha256"] != binding.sha(folder / diagnosis_name)
                or len(row["rejection_controls_passed"]) != expected_rejections
                or row["executed_test_sha256"] != manifest["copied_files"][test_name]):
            raise ValueError("mixed interface lacks actual mode-specific arithmetic controls")
        for module_name in module_names:
            if constant.original_test_module_digest(row, module_name) != manifest["copied_files"][module_name]:
                raise ValueError("mixed mode arithmetic controls used different exact modules")
    guard = binding.read(folder / "INTERFACE-GUARD-CONTROLS.json")
    if (guard["schema"] != "N26-mixed-curvature-cover-interface-guard-controls-v1"
            or guard["metadata_guard_controls_passed"] is not True
            or len(guard["actual_arithmetic_rejection_control_paths_exercised"]) != 29
            or guard["complete_latest_model_source_history_gate_NOT_executed"] is not True
            or guard["verified"] is not False
            or guard["new_geometric_payments"] != 0
            or guard["candidate_whole_roots_removed"] != 0
            or guard["tested_own_acceptance_executor_sha256"] != binding.sha(__file__)
            or guard["executed_test_sha256"] != manifest["copied_files"][
                "test_mixed_candidate_curvature_cover_interface.py"]
            or guard["tested_integral_backend_sha256"] != manifest["copied_files"][
                "n26_integrated_hull_local_cover.py"]):
        raise ValueError("mixed interface guard evidence changed or became a source-replay shortcut")
    return manifest, first, second


def input_gate(folder):
    manifest, first, second = metadata_gate(folder)
    source = binding.local_path(manifest["source"])
    source_replay = binding.local_path(manifest["source_replay"])
    parent_path = binding.local_path(manifest["parent_current_audit"])
    rehash_path = binding.local_path(manifest["parent_digest_recheck"])
    parent, rehash = binding.read(parent_path), binding.read(rehash_path)
    if (binding.sha(parent_path) != manifest["parent_current_audit_sha256"]
            or binding.sha(rehash_path) != manifest["parent_digest_recheck_sha256"]
            or binding.read(folder / "SOURCE-CURRENT-AUDIT.json") != parent
            or binding.read(folder / "SOURCE-FINAL-DIGEST-RECHECK.json") != rehash):
        raise ValueError("mixed interface changed its actual completed owned proof-time parent")
    layer = constant.identity.gate(parent, manifest["parent_current_audit_sha256"], source)
    print("Replaying COMPLETE original latest owned model, every old payment and root forest.",
          flush=True)
    accepted, values, incoming, inventory, previous_payments = constant.owned.gate(
        source, source_replay, parent_path, rehash_path)
    if (accepted["schema"] != constant.owned.SCHEMA
            or binding.sha(source / "VERIFIED.json") != manifest["source_acceptance_sha256"]
            or binding.read(folder / "SOURCE-ACCEPTANCE.json") != accepted
            or binding.read(folder / "SOURCE-PENDING-ANGLES.json") != incoming
            or len(incoming) != parent["candidate_angle_unresolved_closed_boxes"]
            or F(values[3]["radius"]) != F(parent["r_strict_interval"][1])):
        raise ValueError("mixed curvature changed actual latest model, radius or whole-root rows")
    history, paths = constant.owned.history(source, incoming)
    inventory.extend(paths)
    constant.history_gate(binding.read(folder / "SOURCE-ROOT-HISTORY.json"), history)
    roots = binding.read(folder / "COVERS.json")
    if roots != selected_covers(first, second):
        raise ValueError("mixed interface changed, omitted or relabelled its explicit mode certificates")
    modes_gate(roots)
    constant.root_gate(incoming, roots)
    inventory.extend((parent_path, rehash_path, source_replay))
    return (manifest, parent, accepted, values, incoming, roots, history,
            inventory, previous_payments, layer)


def derive(values, roots_override=None):
    _, _, _, original_values, incoming, roots, history, _, _, _ = values
    roots = roots if roots_override is None else roots_override
    modes_gate(roots)
    by_index = constant.root_gate(incoming, roots)
    original, kernel, arcs = original_values[3], original_values[5], original_values[6]
    payments, classified = [], []
    for item in roots:
        index, mode, cover = item["source_OPEN_index"], item["mode"], item["cover"]
        if mode == MODES[0]:
            result = constant.covers.replay(original, kernel, arcs, by_index[index], cover)
            strict = result["strict_signed_hull_energy_slabs"]
        else:
            result = integral.replay(original, kernel, arcs, by_index[index], cover)
            strict = result["strict_integrated_slabs_checked"]
        payments.append({
            "source_OPEN_index": index, "actual_source_closed_box": by_index[index],
            "source_candidate_root_fully_lower_bounded": True,
            "source_candidate_root_strictly_empty": False,
            "original_LOCAL_central_box_preserves_equality_feasibility": True,
            "mode": mode, "supplemental_cover_arithmetic": result,
            "latest_accepted_forest_kept_as_unchanged_prior_proof": history.get(index),
        })
        classified.append({"source_OPEN_index": index, "mode": mode,
                           "strict_slabs": strict, "original_LOCAL_boxes": 1,
                           "arithmetic_result": result})
        print(json.dumps({"mixed_root_replayed": index, "mode": mode,
                          "strict_slabs": strict}), flush=True)
    discharged = {item["source_OPEN_index"] for item in payments}
    remaining = [row for row in incoming if row["index"] not in discharged]
    retained = [history[index] for index in sorted(history) if index not in discharged]
    if len(payments) + len(remaining) != len(incoming):
        raise ValueError("mixed-curvature root conservation failed")
    return payments, remaining, classified, retained


def controls(values):
    _, _, _, original_values, incoming, roots, history, _, _, _ = values
    modes_gate(roots)
    constants = [item["cover"] for item in roots if item["mode"] == MODES[0]]
    integrals = [item["cover"] for item in roots if item["mode"] == MODES[1]]
    old_values = (*values[:5], constants, *values[6:])
    old_positive, old_negative = constant.controls(old_values)
    original, kernel, arcs = original_values[3], original_values[5], original_values[6]
    by_index = constant.root_gate(incoming, roots)
    first = integrals[0]
    integral_negative = integral.rejection_controls(
        original, kernel, arcs, by_index[first["source_OPEN_index"]], first)
    negatives = ["constant:" + label for label in old_negative]
    negatives.extend("integral:" + label for label in integral_negative)

    def reject(label, mutation):
        bad = deepcopy(roots)
        mutation(bad)
        try:
            derive(values, bad)
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid mixed-curvature mode accepted: " + label)

    first_integral = next(index for index, item in enumerate(roots) if item["mode"] == MODES[1])
    first_constant = next(index for index, item in enumerate(roots) if item["mode"] == MODES[0])
    reject("mixed:duplicate-root-across-modes",
           lambda bad: bad.__setitem__(first_integral, {
               **deepcopy(bad[first_constant]), "mode": MODES[1]}))
    reject("mixed:unknown-curvature-mode",
           lambda bad: bad[first_constant].update(mode="unproved-new-mode"))
    reject("mixed:constant-cover-relabelled-as-integral",
           lambda bad: bad[first_constant].update(mode=MODES[1]))
    reject("mixed:integral-cover-relabelled-as-constant",
           lambda bad: bad[first_integral].update(mode=MODES[0]))
    integral_positive = [integral.tiny_control(original, kernel, arcs, item)
                         for item in integrals]
    if len(negatives) != 29:
        raise ValueError("mixed-curvature acceptance omitted a real required control")
    return {
        "original_full_source_positive_controls": old_positive[
            "original_full_source_positive_controls"],
        "constant_hull_tiny_controls": old_positive["fresh_signed_hull_feasible_tiny_controls"],
        "integrated_Taylor_tiny_controls": integral_positive,
    }, negatives


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    values = input_gate(folder)
    manifest, parent, _, original_values, incoming, _, history, inventory, _, layer = values
    payments, remaining, classified, retained = derive(values)
    positives, negatives = controls(values)
    certificate = {
        "schema": "N26-accepted-mixed-curvature-LOCAL-root-cover-certificate-v1",
        "radius_scope": "same-root-Rstar", "radius_upper": str(original_values[3]["radius"]),
        "discharged_actual_source_root_indices": [row["source_OPEN_index"] for row in payments],
        "all_uncovered_whole_roots_and_latest_partial_histories_retained": True,
        "supplemental_cover_does_not_replace_prior_forest": True,
        "LOCAL_lower_bound_is_not_an_emptiness_claim": True,
        "accepted_curvature_modes": MODES,
    }
    outputs = {
        "CERTIFICATE.json": certificate, "ROOT-PAYMENTS.json": payments,
        "PENDING-ANGLES.json": remaining, "ROOT-CLASSIFICATION.json": classified,
        "REMAINING-ROOT-HISTORY.json": retained, "POSITIVE-CONTROLS.json": positives,
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
        "accepted_curvature_modes": MODES,
        "supplemental_strict_energy_slabs": sum(row["strict_slabs"] for row in classified),
        "supplemental_original_LOCAL_central_boxes": len(classified),
        "mode_root_counts": {mode: sum(row["mode"] == mode for row in classified) for mode in MODES},
        "overlapping_slabs_not_counted_as_new_unique_old_forest_leaves": True,
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
        "negative_controls_rejected": negatives,
        "feasible_signed_curvature_candidate_controls": sum(
            len(positives[key]) for key in ("constant_hull_tiny_controls", "integrated_Taylor_tiny_controls")),
        "retained_prior_history_entries": len(history),
        "files": {name: binding.sha(folder / name) for name in dict.fromkeys(
            ["MANIFEST.json", *manifest["copied_files"], *outputs])},
        "source_files": digests, "executed_checker_file": CHECKER,
        "executed_checker_sha256": binding.sha(__file__),
    }
    if report["executed_checker_sha256"] != report["files"][CHECKER]:
        raise ValueError("mixed-curvature report relabelled another executor")
    for text, digest in digests.items():
        if binding.sha(text) != digest:
            raise ValueError("mixed-curvature full source/history changed during final binding")
    for text, digest in parent["files"].items():
        if binding.sha(text) != digest:
            raise ValueError("mixed-curvature completed current parent changed during final binding")
    if binding.sha(binding.local_path(manifest["parent_current_audit"])) != manifest[
            "parent_current_audit_sha256"]:
        raise ValueError("mixed-curvature proof-time snapshot changed")
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
