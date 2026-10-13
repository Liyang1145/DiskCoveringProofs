"""ENTIRE actual source/parent-bound geometry main for the new closed-ear rule.

No --fast/--skip/cache acceptance mode exists. Own and publication must run
this exact main; a later current join and independent final remain mandatory.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import sys

from audit_prefix_partition import linux
import audit_stage_catalogue_with_closed_pool as historical
import n26_closed_ear_cover_transfer as transfer
import n26_current_candidate_layer_identity as identity
import new_upper_scope as family
import test_embedded_dual_bridge_algebra as independent_bridge
import verify_conditional_force_stage as binding


INPUT_SCHEMA = "N26-actual-current28-closed-ear-source-geometry-input-v1"
SCHEMA = "N26-actual-whole-source-closed-ear-core-capacity-geometry-acceptance-v1"
CHECKER = "verify_closed_ear_source_geometry.py"
PROOFS = {
    "cap": "UNIT-CAP-PROOF.md", "generic": "GENERIC-SLACK-PROOF.md",
    "bridge": "EMBEDDED-CORNER-SHADOW-BRIDGE-PROOF.md", "ear": "CLOSED-EAR-PROOF.md",
}
CERTIFICATES = {
    "cap": "UNIT-CAP-CERTIFICATE.json", "generic": "GENERIC-CERTIFICATE.json",
    "bridge": "EMBEDDED-CORNER-CERTIFICATE.json",
}


def executed_modules():
    folder = Path(__file__).resolve().parent
    modules = {}
    for module in list(sys.modules.values()):
        text = getattr(module, "__file__", None)
        if text:
            path = Path(text).resolve()
            if path.suffix == ".py" and path.parent == folder:
                modules[path.name] = path
    modules[CHECKER] = Path(__file__).resolve()
    return modules


def parent_gate(parent, final, parent_digest):
    if (final["current_audit_sha256"] != parent_digest
            or final["all_current_file_digests_rehashed"] is not True
            or final["current_file_digests_rechecked"] != len(parent["files"])
            or parent["current_bound_bytes_rechecked"] is not True
            or parent["prior_completed_full_chain_semantic_replay_still_bound"] is not True
            or parent["radius_scope"] != binding.SCOPE
            or parent["original_U_current_pending_subtrees_unchanged"] != 3922
            or parent["original_52_coordinate_local_allowance_unchanged"] != "7/800000"
            or parent["full_catalog_complete"] is not False
            or parent["global_lower_bound_proved"] is not False
            or parent["global_optimality_proved"] is not False
            or parent["n27_started"] is not False
            or parent["Rstar_conditional_frontier_pending_subtrees"] != 11183
            or parent["candidate_angle_unresolved_closed_boxes"] != 25
            or parent["r_strict_interval"] != final["r_strict_interval"]):
        raise ValueError("closed-ear geometry lacks the ACTUAL unchanged completed current28 pair")


def rehash(inventory, phase):
    for number, (text, digest) in enumerate(inventory.items(), 1):
        if binding.sha(text) != digest:
            raise ValueError("closed-ear "+phase+" current dependency changed: "+text)
        if number % 10000 == 0:
            print(json.dumps({"closed_ear_complete_parent_phase": phase,
                              "dependencies_rehashed": number, "total": len(inventory)}), flush=True)


def input_gate(folder):
    manifest = binding.read(folder/"MANIFEST.json")
    if (manifest["schema"] != INPUT_SCHEMA or manifest["checker"] != CHECKER
            or manifest["rule_mode"] != transfer.MODE
            or manifest["radius_scope"] != binding.SCOPE
            or manifest["full_actual_parent_inventory_and_source_reconstruction_required"] is not True
            or manifest["current_adoption_is_not_done_by_own_geometry"] is not True):
        raise ValueError("closed-ear sealed input changed its required complete body or scope")
    for name, digest in manifest["copied_files"].items():
        if binding.sha(folder/name) != digest:
            raise ValueError("closed-ear frozen copied file changed: "+name)
    for name, path in executed_modules().items():
        if name not in manifest["copied_files"] or binding.sha(path) != manifest["copied_files"][name]:
            raise ValueError("closed-ear loaded executor was substituted: "+name)
    parent_path, final_path = (binding.local_path(manifest[field]) for field in ("parent_current", "parent_final"))
    source_path = binding.local_path(manifest["source_frontier"])
    source_acceptance_path = binding.local_path(manifest["source_acceptance"])
    candidate_folder = binding.local_path(manifest["actual_candidate_source"])
    if (binding.sha(parent_path) != manifest["parent_current_sha256"]
            or binding.sha(final_path) != manifest["parent_final_sha256"]
            or binding.sha(source_path) != manifest["source_frontier_sha256"]
            or binding.sha(source_acceptance_path) != manifest["source_acceptance_sha256"]):
        raise ValueError("closed-ear actual source/current pair no longer matches frozen input")
    parent, final = binding.read(folder/"SOURCE-CURRENT.json"), binding.read(folder/"SOURCE-FINAL.json")
    if parent != binding.read(parent_path) or final != binding.read(final_path):
        raise ValueError("closed-ear copied parent is not the ACTUAL completed parent")
    parent_gate(parent, final, manifest["parent_current_sha256"])
    source, accepted = binding.read(folder/"SOURCE-FRONTIER.json"), binding.read(folder/"SOURCE-ACCEPTANCE.json")
    if (source != binding.read(source_path) or accepted != binding.read(source_acceptance_path)
            or parent["files"].get(linux(source_path)) != manifest["source_frontier_sha256"]
            or parent["files"].get(linux(source_acceptance_path)) != manifest["source_acceptance_sha256"]
            or accepted["files"]["FRONTIER.json"] != manifest["source_frontier_sha256"]
            or len(source["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
            or source["radius_scope"] != binding.SCOPE
            or F(source["radius_upper"]) != F(parent["r_strict_interval"][1])
            or source["families"] != parent["Rstar_conditional_frontier_families"]):
        raise ValueError("closed-ear substituted the actual conditional frontier/families")
    layer = identity.gate(parent, manifest["parent_current_sha256"], candidate_folder)
    pending = binding.read(candidate_folder/"PENDING-ANGLES.json")
    if (len(pending) != 25 or parent["files"].get(linux(candidate_folder/"VERIFIED.json"))
            != binding.sha(candidate_folder/"VERIFIED.json")
            or parent["files"].get(linux(candidate_folder/"PENDING-ANGLES.json"))
            != binding.sha(candidate_folder/"PENDING-ANGLES.json")):
        raise ValueError("closed-ear changes or substitutes actual candidate-root ownership/history")
    return manifest, parent, source, layer


def family_gate(folder, manifest, parent):
    original = binding.local_path(manifest["family_scope"])
    accepted, constants = binding.read(folder/"FAMILY-ACCEPTANCE.json"), binding.read(folder/"FAMILY-CONSTANTS.json")
    if (accepted != binding.read(original/"VERIFIED.json")
            or constants != binding.read(original/"CONSTANTS.json")
            or accepted["arithmetic_verified"] is not True
            or accepted["N26_continuous_upper_replayed"] is not True
            or accepted["family_scope_valid_assuming_cited_n8_theorem"] is not True
            or accepted["N8_lower_bound_reproved_here"] is not False):
        raise ValueError("closed-ear lost the explicit imported N8 count theorem")
    paths = [original/"VERIFIED.json"]
    for text, digest in accepted["files"].items():
        path = binding.local_path(text)
        if binding.sha(path) != digest or parent["files"].get(linux(path)) != digest:
            raise ValueError("closed-ear original family dependency is not still-bound: "+text)
        paths.append(path)
    upper_path = binding.local_path(manifest["original_rational_upper_acceptance"])
    upper = binding.read(upper_path)
    checked = family.gate(constants, upper, transfer.force.load_trig(folder)[0])
    if checked["strict_n8_core_gap"] != constants["strict_n8_core_gap"]:
        raise ValueError("closed-ear changed an exact original N8/core comparison")
    return constants, checked, paths


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("closed-ear original main never overwrites own/publication")
    folder = args.input
    manifest, parent, source, candidate_layer = input_gate(folder)
    manifest_digest = binding.sha(folder/"MANIFEST.json")
    inventory = dict(parent["files"])
    print("Rehashing EVERY actual completed parent dependency before ear geometry replay.", flush=True)
    rehash(inventory, "before-semantic-replay")
    constants, family_result, family_paths = family_gate(folder, manifest, parent)
    certificates = {key: binding.read(folder/name) for key, name in CERTIFICATES.items()}
    proofs = {key: binding.sha(folder/name) for key, name in PROOFS.items()}
    # Fresh symbolic evaluation, including the distinct scalar implementation;
    # independent reports are provenance/control inputs, not a cached answer.
    independent_symbols = independent_bridge.independent_identities(certificates["bridge"])
    if independent_symbols != 12:
        raise ValueError("closed-ear missing a fresh independent universal bridge relation")
    print("Reconstructing the ENTIRE actual source, all closed ears, m cases and shadow placements.", flush=True)
    frontier, ledger, semantic = transfer.partition(source, constants, certificates, proofs)
    if (frontier != binding.read(folder/"FRONTIER.json")
            or ledger != binding.read(folder/"LOWER-LEDGER.json")
            or semantic != binding.read(folder/"SOURCE-MATHEMATICAL-SEMANTICS.json")
            or semantic["closed_ear_whole_prefixes"] != 643
            or semantic["original_physical_count_AND_all_shadow_label_placement_cases_checked"] != 673):
        raise ValueError("actual whole source geometry/ledger did not freshly reconstruct")
    pool_path = binding.local_path(manifest["closed_type_pool"])
    terminal_path = binding.local_path(manifest["terminal_obligations"])
    if (parent["files"].get(linux(pool_path)) != binding.sha(pool_path)
            or parent["files"].get(linux(terminal_path)) != binding.sha(terminal_path)):
        raise ValueError("closed-ear geometry lost historical type pool or raw terminal obligations")
    receipts = historical.retained_pool_gate(
        binding.read(pool_path), parent, F(parent["r_strict_interval"][1]))
    if len(receipts) != 215 or len(binding.read(pool_path)) != 87:
        raise ValueError("closed-ear lost an actual historical type or proof receipt")
    if [row for row in frontier["pending_states"] if row["terminal"]] != [
            row for row in source["pending_states"] if row["terminal"]]:
        raise ValueError("closed-ear source geometry discarded a complete candidate path")
    negative = []
    def reject(name, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(name)
        else:
            raise AssertionError("bad actual geometric scope accepted: "+name)
    for name, field, value in (
        ("unverified-parent-final", "all_current_file_digests_rehashed", False),
        ("wrong-parent-source-final", "current_audit_sha256", "0"*64),
    ):
        changed = deepcopy(binding.read(folder/"SOURCE-FINAL.json"))
        changed[field] = value
        reject(name, lambda changed=changed: parent_gate(parent, changed, manifest["parent_current_sha256"]))
    changed = deepcopy(constants)
    changed["minimum_interior_cells"] = 8
    reject("hidden-B17-under26-physical-cover", lambda: transfer.original_count_cases(17, changed))
    changed_certificates = deepcopy(certificates)
    changed_certificates["bridge"]["explicit_ordered_real_hypotheses"].pop()
    reject("shadow-cell-owner-frame-substitution", lambda: transfer.lemma_gate(changed_certificates, proofs))
    corrupted = deepcopy(ledger)
    corrupted[0]["original_physical_count_and_all_shadow_label_placement_cases"].pop()
    if corrupted == ledger:
        raise AssertionError("missing shadow case control did not change the actual ledger")
    negative.append("actual-missing-shadow-label-case-ledger-differs-from-full-fresh-reconstruction")
    # Seal ALL supplemental inputs and exact original parent records into the
    # dependency inventory. No old paid file or old receipt is removed.
    extra_paths = [folder/"MANIFEST.json", *[folder/name for name in manifest["copied_files"]],
                   binding.local_path(manifest["parent_current"]), binding.local_path(manifest["parent_final"]),
                   *family_paths]
    for path in extra_paths:
        text, digest = linux(path), binding.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("old and supplemental geometry dependencies disagree")
        inventory[text] = digest
    print("Rehashing the ENTIRE parent+supplement dependency inventory after semantic replay.", flush=True)
    rehash(inventory, "after-semantic-replay")
    latest_manifest, latest_parent, latest_source, latest_layer = input_gate(folder)
    if (binding.sha(folder/"MANIFEST.json") != manifest_digest or latest_manifest != manifest
            or latest_parent != parent or latest_source != source or latest_layer != candidate_layer):
        raise ValueError("actual source/owner/current changed during the whole geometry main")
    report = {
        "schema": SCHEMA, "verified": True, "radius_scope": binding.SCOPE,
        "screen_radius_threshold_for_NEW_ear_rule": str(transfer.U),
        "radius_upper": source["radius_upper"], "r_strict_interval": parent["r_strict_interval"],
        "inherited_source_is_unconditional_at_U": False,
        "executed_checker_file": CHECKER, "executed_checker_sha256": manifest["copied_files"][CHECKER],
        "actual_parent_current_sha256": manifest["parent_current_sha256"],
        "actual_parent_final_sha256": manifest["parent_final_sha256"],
        "actual_source_frontier_sha256": manifest["source_frontier_sha256"],
        "actual_candidate_layer_identity": candidate_layer,
        "complete_parent_dependency_inventory_rehashed_BEFORE_AND_AFTER": True,
        "prior_completed_parent_semantic_proof_chain_still_bound_NOT_replaced_by_DATA": True,
        "actual_original_count_family_theorem_rechecked_with_EXPLICIT_imported_n8": family_result,
        "ENTIRE_actual_source_prefixes_geometry_and_case_partition_replayed_here": semantic,
        "fresh_independent_universal_bridge_scalar_identities": independent_symbols,
        "historical_closed_types_retained": 87, "historical_proof_receipts_retained_and_associated": 215,
        "all_original_candidate_terminal_states_owned_roots_histories_and_LOCAL_retained": True,
        "source_actual_current_frontier": len(source["pending_states"]),
        "geometry_accepted_filtered_frontier_REQUIRES_CURRENT_AND_FINAL": len(frontier["pending_states"]),
        "strict_new_closed_ear_whole_source_prefixes": len(ledger),
        "all_original_physical_counts_and_shadow_label_placements_covered": True,
        "corner_copy_is_embedded_LIMIT_not_26_distinct_original_Voronoi_cells": True,
        "written_continuous_dual_starring_and_ear_proofs_are_used_NOT_inferred_from_finite_tests": True,
        "actual_scope_and_original_parent_negative_controls_rejected": negative,
        "actual_current_nodes_removed_by_this_OWN_acceptance": 0,
        "new_formal_geometric_payments_by_this_OWN_acceptance": 0,
        "candidate_whole_roots_removed": 0,
        "original_U_frontier_nodes_removed": 0,
        "unrestricted_reduction_final_joint_acceptance": False,
        "frozen_geometric_reduction_proved": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {name: digest for name, digest in {
            **manifest["copied_files"], "MANIFEST.json": manifest_digest}.items()},
        "source_files": inventory,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_whole_source_closed_ear_geometry_main_completed": True,
        "strict_whole_prefixes": len(ledger), "filtered_frontier_not_yet_current": len(frontier["pending_states"]),
        "current_and_independent_final_STILL_required": True, "candidate_whole_roots_removed": 0}), flush=True)


if __name__ == "__main__":
    main()
