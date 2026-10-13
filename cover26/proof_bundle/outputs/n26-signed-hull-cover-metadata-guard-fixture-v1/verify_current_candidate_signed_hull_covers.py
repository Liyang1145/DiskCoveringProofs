"""Own-executor acceptance for supplemental signed-hull/LOCAL root covers.

The unchanged full owned-candidate source gate reconstructs the actual model,
all old payments and every current per-root forest. The supplemental covers
never replace those forests. Typed diagnostic contexts are not imported here.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_current_candidate_layer_identity as identity
import n26_current_owned_candidate_source as owned
import n26_signed_hull_local_cover as covers
import verify_conditional_force_stage as binding
import verify_owned_candidate_forests as prior_checker


INPUT_SCHEMA = "N26-current-signed-hull-LOCAL-supplemental-cover-bindings-v1"
SCHEMA = "N26-accepted-current-signed-hull-LOCAL-supplemental-root-covers-v1"
CHECKER = "verify_current_candidate_signed_hull_covers.py"
DIAGNOSES = {
    "N26-unaccepted-adaptive-signed-hull-LOCAL-zero-dual-diagnosis-v1",
}


def history_gate(snapshot, history):
    expected = [history[index] for index in sorted(history)]
    if snapshot != expected:
        raise ValueError("supplemental cover changed newest accepted per-root forest history")
    return expected


def original_test_module_digest(regression, name):
    matches = [digest for text, digest in regression["modules"].items()
               if binding.local_path(text).name == name]
    if len(matches) != 1:
        raise ValueError("arithmetic control has missing or ambiguous original module identity")
    return matches[0]


def root_gate(incoming, proposed):
    if (not isinstance(incoming, list) or not isinstance(proposed, list)
            or not proposed):
        raise ValueError("supplemental cover requires explicit remaining roots and covers")
    by_index = {row["index"]: row for row in incoming}
    if (len(by_index) != len(incoming)
            or any(type(index) is not int for index in by_index)):
        raise ValueError("supplemental cover incoming root ownership is malformed")
    seen = set()
    for item in proposed:
        index = item["source_OPEN_index"]
        if type(index) is not int or index in seen or index not in by_index:
            raise ValueError("supplemental cover duplicated, invented or reopened a paid root")
        if item["actual_source_closed_box"] != by_index[index]:
            raise ValueError("supplemental cover clipped or changed an entire actual current root")
        seen.add(index)
    return by_index


def metadata_gate(folder):
    manifest = binding.read(folder / "MANIFEST.json")
    if (manifest["schema"] != INPUT_SCHEMA
            or manifest["radius_scope"] != "same-root-Rstar"
            or manifest["acceptance_checker_file"] != CHECKER
            or manifest["typed_resource_not_a_source_replay_substitute"] is not True
            or manifest["supplemental_cover_never_replaces_accepted_forest"] is not True):
        raise ValueError("supplemental cover changed its acceptance executor or source scope")
    for name, digest in manifest["copied_files"].items():
        if binding.sha(folder / name) != digest:
            raise ValueError("supplemental cover sealed input changed: " + name)
    for module in (identity, owned, covers, covers.hull, covers.forest, prior_checker):
        if binding.sha(module.__file__) != manifest["copied_files"][Path(module.__file__).name]:
            raise ValueError("supplemental cover executes different sealed source/geometry arithmetic")
    if (Path(__file__).name != CHECKER
            or binding.sha(__file__) != manifest["copied_files"][CHECKER]):
        raise ValueError("supplemental cover does not bind its actual own executor")
    diagnosis = binding.read(folder / "DIAGNOSIS.json")
    if (diagnosis["schema"] not in DIAGNOSES or diagnosis["verified"] is not False
            or diagnosis["new_geometric_payments"] != 0
            or diagnosis["current_candidate_whole_roots_removed"] != 0):
        raise ValueError("supplemental cover relabelled a discovery as an accepted proof")
    regression = binding.read(folder / "ARITHMETIC-COVER-CONTROLS.json")
    if (regression["all_arithmetic_cover_reconstructions_passed"] is not True
            or regression["arithmetic_only_not_a_geometric_source_or_ownership_replay"] is not True
            or regression["full_source_model_history_replay_not_performed"] is not True
            or regression["new_geometric_payments"] != 0
            or regression["candidate_whole_roots_removed"] != 0
            or regression["diagnosis_sha256"] != binding.sha(folder / "DIAGNOSIS.json")
            or len(regression["rejection_controls_passed"]) != 11
            or original_test_module_digest(regression, Path(covers.__file__).name)
            != manifest["copied_files"][Path(covers.__file__).name]
            or original_test_module_digest(regression, Path(covers.hull.__file__).name)
            != manifest["copied_files"][Path(covers.hull.__file__).name]):
        raise ValueError("supplemental cover lacks this lemma's original arithmetic controls")
    # Original diagnostic module paths differ from the frozen execution path.
    # Bind hashes, not a relabelled executor path.
    if regression["executed_test_sha256"] != manifest["copied_files"][
            "test_signed_hull_local_cover_arithmetic.py"]:
        raise ValueError("supplemental cover arithmetic test executor changed")
    return manifest, diagnosis


def input_gate(folder):
    manifest, diagnosis = metadata_gate(folder)
    source_folder = binding.local_path(manifest["source"])
    replay_path = binding.local_path(manifest["source_replay"])
    parent_path = binding.local_path(manifest["parent_current_audit"])
    rehash_path = binding.local_path(manifest["parent_digest_recheck"])
    parent, rehash = binding.read(parent_path), binding.read(rehash_path)
    if (binding.sha(parent_path) != manifest["parent_current_audit_sha256"]
            or binding.sha(rehash_path) != manifest["parent_digest_recheck_sha256"]
            or binding.read(folder / "SOURCE-CURRENT-AUDIT.json") != parent
            or binding.read(folder / "SOURCE-FINAL-DIGEST-RECHECK.json") != rehash):
        raise ValueError("supplemental cover substituted its completed proof-time current parent")
    actual_layer = identity.gate(
        parent, manifest["parent_current_audit_sha256"], source_folder)
    print("Replaying the COMPLETE latest owned candidate model, roots and every old payment.",
          flush=True)
    accepted, values, incoming, inventory, previous_payments = owned.gate(
        source_folder, replay_path, parent_path, rehash_path)
    if (accepted["schema"] != owned.SCHEMA
            or binding.sha(source_folder / "VERIFIED.json")
            != manifest["source_acceptance_sha256"]
            or binding.read(folder / "SOURCE-ACCEPTANCE.json") != accepted
            or binding.read(folder / "SOURCE-PENDING-ANGLES.json") != incoming
            or len(incoming) != parent["candidate_angle_unresolved_closed_boxes"]
            or F(values[3]["radius"]) != F(parent["r_strict_interval"][1])):
        raise ValueError("supplemental cover changed the actual newest owned source/model or roots")
    history, paths = owned.history(source_folder, incoming)
    inventory.extend(paths)
    history_gate(binding.read(folder / "SOURCE-ROOT-HISTORY.json"), history)
    roots = binding.read(folder / "COVERS.json")
    selected = [item for item in diagnosis["roots"]
                if item["all_arithmetic_cover_obligations_passed"]]
    if roots != selected:
        raise ValueError("supplemental cover omitted or changed its explicit discovery certificates")
    root_gate(incoming, roots)
    inventory.extend((parent_path, rehash_path, replay_path))
    return (manifest, parent, accepted, values, incoming, roots, history,
            inventory, previous_payments, actual_layer)


def derive(values, roots_override=None):
    _, _, _, original_values, incoming, roots, history, _, _, _ = values
    proposed = roots if roots_override is None else roots_override
    by_index = root_gate(incoming, proposed)
    original, kernel, arcs = original_values[3], original_values[5], original_values[6]
    payments, classified = [], []
    for item in proposed:
        index = item["source_OPEN_index"]
        result = covers.replay(original, kernel, arcs, by_index[index], item)
        payments.append({
            "source_OPEN_index": index, "actual_source_closed_box": by_index[index],
            "source_candidate_root_fully_lower_bounded": True,
            "source_candidate_root_strictly_empty": False,
            "original_LOCAL_central_box_preserves_equality_feasibility": True,
            "supplemental_cover_arithmetic": result,
            "latest_accepted_forest_kept_as_unchanged_prior_proof":
                history.get(index),
        })
        classified.append({"source_OPEN_index": index, **result})
        print(json.dumps({"fresh_signed_hull_root_replayed": index,
                          "strict_slabs": result["strict_signed_hull_energy_slabs"]}),
              flush=True)
    indices = {item["source_OPEN_index"] for item in payments}
    remaining = [row for row in incoming if row["index"] not in indices]
    retained_history = [history[index] for index in sorted(history) if index not in indices]
    if len(payments) + len(remaining) != len(incoming):
        raise ValueError("supplemental cover lost whole-root accounting")
    return payments, remaining, classified, retained_history


def controls(values):
    _, _, _, original_values, incoming, roots, history, _, _, _ = values
    negatives = []

    def reject(label, change):
        bad = deepcopy(roots)
        change(bad)
        try:
            derive(values, bad)
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid supplemental signed-hull cover accepted: " + label)

    reject("duplicate-whole-root-payment", lambda bad: bad.append(deepcopy(bad[0])))
    paid_index = next(index for index in (1794, 957)
                      if index not in {row["index"] for row in incoming})
    reject("previously-paid-whole-root-reopened",
           lambda bad: bad[0].update(source_OPEN_index=paid_index))
    reject("whole-root-sharp-domain-clipped",
           lambda bad: bad[0]["actual_source_closed_box"]["sharp_lower"].__setitem__(0, "0"))
    reject("first-closed-slab-omitted",
           lambda bad: bad[0]["sequential_closed_slabs"].pop(0))
    reject("hidden-additional-slab",
           lambda bad: bad[0]["sequential_closed_slabs"].append(
               deepcopy(bad[0]["sequential_closed_slabs"][0])))
    reject("shared-closed-cut-boundary-lost",
           lambda bad: bad[0]["sequential_closed_slabs"][0].update(
               both_closed_halves_include_shared_cut=False))
    reject("central-LOCAL-remainder-clipped",
           lambda bad: bad[0]["central_closed_box"]["closed_lower"].__setitem__(0, "0"))
    first_eta = roots[0]["sequential_closed_slabs"][0]["certificate"]["signed_eta"]
    free_axis = next(axis for axis, value in enumerate(first_eta) if F(value) < 0)
    reject("positive-curvature-unsupported-by-exact-LDL",
           lambda bad: bad[0]["sequential_closed_slabs"][0]["certificate"]["signed_eta"].__setitem__(
               free_axis, "-1000000"))
    reject("negative-difference-dual-multiplier",
           lambda bad: bad[0]["sequential_closed_slabs"][0]["certificate"]["difference_dual"].update(
               terms=[[0, 1, "-1"]]))
    reject("reference-outside-necessary-polytope",
           lambda bad: bad[0]["sequential_closed_slabs"][0]["certificate"]["reference_turns"].__setitem__(
               0, "100"))
    reject("LOCAL-coordinate-allowance-expanded",
           lambda bad: bad[0]["central_closed_box"]["original_LOCAL_result"].update(
               original_52_coordinate_local_allowance="1"))
    reject("discovery-arithmetic-result-substituted",
           lambda bad: bad[0]["sequential_closed_slabs"][0]["arithmetic_result"].update(
               minimum_strict_energy_margin="1"))
    if history:
        bad_history = [deepcopy(history[index]) for index in sorted(history)]
        bad_history[0]["nodes"] = [{"kind": "OPEN"}]
        try:
            history_gate(bad_history, history)
        except ValueError:
            negatives.append("latest-accepted-non-OPEN-history-reset")
        else:
            raise AssertionError("supplemental cover reset the latest accepted forest")
    else:
        raise ValueError("this supplemental acceptance requires actual nonempty owned history")
    positives = prior_checker.base.source.tiny_control(original_values)
    original, kernel, arcs = original_values[3], original_values[5], original_values[6]
    tiny = [tuple(map(F, pair))
            for pair in original["cap"]["known_candidate_tiny_angle_cells"]]
    tiny_box = covers.tighten(original["matrix"], [a for a, _ in tiny], [c for _, c in tiny])
    signed_positives = []
    for item in roots:
        suggested = item["sequential_closed_slabs"][0]["certificate"]
        certificate = {**suggested, "difference_dual": {"q": 1, "terms": []}}
        result = covers.hull.bound(
            kernel, original["matrix"], *tiny_box, certificate, original["radius"], arcs)
        if result["arithmetic_strict_exclusion_test_passed"]:
            raise AssertionError("supplemental signed-hull verifier excludes the feasible tiny candidate")
        signed_positives.append({
            "source_OPEN_index": item["source_OPEN_index"],
            "known_feasible_tiny_candidate_not_strictly_excluded": True})
    return {"original_full_source_positive_controls": positives,
            "fresh_signed_hull_feasible_tiny_controls": signed_positives}, negatives


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    values = input_gate(folder)
    manifest, parent, _, original_values, incoming, _, history, inventory, _, layer = values
    payments, remaining, classified, retained = derive(values)
    positives, negatives = controls(values)
    if len(negatives) != 13:
        raise ValueError("supplemental acceptance omitted an actual rejection control")
    certificate = {
        "schema": "N26-accepted-signed-hull-LOCAL-current-root-cover-certificate-v1",
        "radius_scope": "same-root-Rstar",
        "radius_upper": str(original_values[3]["radius"]),
        "discharged_actual_source_root_indices": [
            item["source_OPEN_index"] for item in payments],
        "all_uncovered_whole_roots_and_latest_partial_histories_retained": True,
        "supplemental_cover_does_not_replace_prior_forest": True,
        "LOCAL_lower_bound_is_not_an_emptiness_claim": True,
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
        "schema": SCHEMA, "verified": True,
        "radius_scope": "same-root-Rstar",
        "radius_upper": str(original_values[3]["radius"]),
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "parent_current_audit_sha256": manifest["parent_current_audit_sha256"],
        "actual_latest_candidate_layer_identity": layer,
        "source_actual_remaining_candidate_roots": len(incoming),
        "new_whole_candidate_source_roots_lower_bounded": len(payments),
        "new_strictly_empty_source_roots": 0,
        "new_source_roots_discharged_with_original_LOCAL": len(payments),
        "unresolved_closed_angle_boxes": len(remaining),
        "supplemental_strict_signed_hull_energy_slabs": sum(
            row["strict_signed_hull_energy_slabs"] for row in classified),
        "supplemental_original_LOCAL_central_boxes": len(classified),
        "overlapping_supplemental_slabs_not_counted_as_new_unique_old_forest_leaves": True,
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
        "feasible_signed_hull_candidate_controls": len(
            positives["fresh_signed_hull_feasible_tiny_controls"]),
        "retained_prior_history_entries": len(history),
        "files": {name: binding.sha(folder / name) for name in dict.fromkeys(
            ["MANIFEST.json", *manifest["copied_files"], *outputs])},
        "source_files": digests,
        "executed_checker_file": CHECKER,
        "executed_checker_sha256": binding.sha(__file__),
    }
    if report["executed_checker_sha256"] != report["files"][CHECKER]:
        raise ValueError("supplemental acceptance relabelled another executor")
    for text, digest in digests.items():
        if binding.sha(text) != digest:
            raise ValueError("supplemental source/history changed during final binding")
    for text, digest in parent["files"].items():
        if binding.sha(text) != digest:
            raise ValueError("supplemental full current parent changed during final binding")
    if binding.sha(binding.local_path(manifest["parent_current_audit"])) != manifest[
            "parent_current_audit_sha256"]:
        raise ValueError("supplemental proof-time current snapshot changed")
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
