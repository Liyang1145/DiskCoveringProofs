"""REAL entire-source/parent-bound geometry main for the stronger six-target rule.

No cached acceptance or fast mode. Same exact main for own/publication/current.
Its own acceptance removes ZERO formal nodes; current and final are separate.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import sys

from audit_prefix_partition import linux
import audit_stage_catalogue_with_closed_pool as historical
import n26_current_candidate_layer_identity as identity
import n26_six_target_cover_transfer as transfer
import test_embedded_dual_bridge_algebra as independent_bridge
import verify_closed_ear_source_geometry as previous
import verify_conditional_force_stage as binding


INPUT_SCHEMA = "N26-actual-current28-six-target-filled-ear-geometry-input-v1"
SCHEMA = "N26-actual-whole-source-six-target-filled-ear-geometry-acceptance-v1"
CHECKER = "verify_six_target_source_geometry.py"
PROOFS = {**previous.PROOFS, "six": "SIX-CORE-TARGET-FILLED-EAR-PROOF.md"}
CERTIFICATES = previous.CERTIFICATES


def executed_modules():
    folder = Path(__file__).resolve().parent
    result = {}
    for module in list(sys.modules.values()):
        text = getattr(module, "__file__", None)
        if text:
            path = Path(text).resolve()
            if path.suffix == ".py" and path.parent == folder:
                result[path.name] = path
    result[CHECKER] = Path(__file__).resolve()
    return result


def input_gate(folder):
    manifest = binding.read(folder/"MANIFEST.json")
    if (
        manifest["schema"] != INPUT_SCHEMA or manifest["checker"] != CHECKER
        or manifest["rule_mode"] != transfer.MODE or manifest["radius_scope"] != binding.SCOPE
        or manifest["full_actual_parent_inventory_and_source_reconstruction_required"] is not True
        or manifest["current_adoption_is_not_done_by_own_geometry"] is not True
        or manifest["old643_geometry_NOT_a_substitute_for_new5546_actual_main"] is not True
    ):
        raise ValueError("six-target geometry changed the required whole body or admission scope")
    for name, digest in manifest["copied_files"].items():
        if binding.sha(folder/name) != digest:
            raise ValueError("six-target frozen copied input changed: "+name)
    for name, path in executed_modules().items():
        if manifest["copied_files"].get(name) != binding.sha(path):
            raise ValueError("six-target loaded executor differs from its frozen copy: "+name)
    parent_path, final_path = (binding.local_path(manifest[field]) for field in ("parent_current", "parent_final"))
    source_path = binding.local_path(manifest["source_frontier"])
    source_acceptance_path = binding.local_path(manifest["source_acceptance"])
    for path, digest in (
        (parent_path, manifest["parent_current_sha256"]), (final_path, manifest["parent_final_sha256"]),
        (source_path, manifest["source_frontier_sha256"]), (source_acceptance_path, manifest["source_acceptance_sha256"]),
    ):
        if binding.sha(path) != digest:
            raise ValueError("six-target actual completed current/source bytes changed")
    parent, final = binding.read(folder/"SOURCE-CURRENT.json"), binding.read(folder/"SOURCE-FINAL.json")
    if parent != binding.read(parent_path) or final != binding.read(final_path):
        raise ValueError("six-target substituted the actual completed current/final pair")
    previous.parent_gate(parent, final, manifest["parent_current_sha256"])
    source, accepted = binding.read(folder/"SOURCE-FRONTIER.json"), binding.read(folder/"SOURCE-ACCEPTANCE.json")
    if (
        source != binding.read(source_path) or accepted != binding.read(source_acceptance_path)
        or parent["files"].get(linux(source_path)) != manifest["source_frontier_sha256"]
        or parent["files"].get(linux(source_acceptance_path)) != manifest["source_acceptance_sha256"]
        or accepted["files"]["FRONTIER.json"] != manifest["source_frontier_sha256"]
        or len(source["pending_states"]) != parent["Rstar_conditional_frontier_pending_subtrees"]
        or source["families"] != parent["Rstar_conditional_frontier_families"]
        or source["radius_scope"] != binding.SCOPE
        or F(source["radius_upper"]) != F(parent["r_strict_interval"][1])
    ):
        raise ValueError("six-target geometry replaced the actual source frontier or radius")
    candidate_folder = binding.local_path(manifest["actual_candidate_source"])
    layer = identity.gate(parent, manifest["parent_current_sha256"], candidate_folder)
    if layer["actual_remaining_candidate_whole_roots"] != 25:
        raise ValueError("six-target geometry substituted a smaller candidate-root objective")
    return manifest, parent, source, layer


def controls_gate(folder, source, manifest):
    producer = binding.read(folder/"SIX-TARGET-MATHEMATICAL-SCAN.json")
    independent = binding.read(folder/"SIX-TARGET-INDEPENDENT-CONTROLS.json")
    if (
        producer["verified"] is not False or independent["verified"] is not False
        or producer["new_formal_geometric_payments"] != 0
        or independent["new_formal_geometric_payments"] != 0
        or producer["actual_qualifying_whole_prefixes"] != 5546
        or independent["independent_qualifying_whole_prefixes"] != 5546
        or independent["entire_original_source_prefixes_independently_reconstructed"] != len(source["pending_states"])
        or independent["independent_original_set_enumeration_cases_checked"] != 58916
        or len(independent["six_target_and_original_owner_and_topology_negative_controls_rejected"]) != 12
        or producer["qualifying_family_counts"] != {"15": 530, "16": 1839, "17": 3177}
        or manifest["mathematical_scan_sha256"] != binding.sha(folder/"SIX-TARGET-MATHEMATICAL-SCAN.json")
        or manifest["independent_controls_sha256"] != binding.sha(folder/"SIX-TARGET-INDEPENDENT-CONTROLS.json")
    ):
        raise ValueError("six-target frozen mathematics lacks its actual entire-source independent controls")
    for record in (producer, independent):
        for text, digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("six-target original mathematical/control provenance changed: "+text)
    return [binding.local_path(text) for record in (producer, independent) for text in record["input_sha256"]]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("preserve own/publication/partial six-target outputs; never repeat a completed main")
    folder = args.input
    manifest, parent, source, layer = input_gate(folder)
    manifest_digest = binding.sha(folder/"MANIFEST.json")
    inventory = dict(parent["files"])
    print("Rehashing EVERY actual current dependency before SIX-target geometry semantics.", flush=True)
    previous.rehash(inventory, "six-target-before-semantic-replay")
    constants, family_result, family_paths = previous.family_gate(folder, manifest, parent)
    provenance_paths = controls_gate(folder, source, manifest)
    certificates = {key: binding.read(folder/name) for key, name in CERTIFICATES.items()}
    proofs = {key: binding.sha(folder/name) for key, name in PROOFS.items()}
    independent_symbols = independent_bridge.independent_identities(certificates["bridge"])
    if independent_symbols != 12:
        raise ValueError("six-target geometry lacks fresh independent universal bridge identities")
    print("Reconstructing ALL original prefixes, proper filled patches and original/shadow cases.", flush=True)
    frontier, ledger, semantic = transfer.partition(source, constants, certificates, proofs)
    if (
        frontier != binding.read(folder/"FRONTIER.json")
        or ledger != binding.read(folder/"LOWER-LEDGER.json")
        or semantic != binding.read(folder/"SOURCE-MATHEMATICAL-SEMANTICS.json")
    ):
        raise ValueError("six-target entire geometric source partition did not freshly reconstruct")
    pool_path = binding.local_path(manifest["closed_type_pool"])
    terminal_path = binding.local_path(manifest["terminal_obligations"])
    if any(parent["files"].get(linux(path)) != binding.sha(path) for path in (pool_path, terminal_path)):
        raise ValueError("six-target source geometry lost historical type/terminal ownership")
    receipts = historical.retained_pool_gate(binding.read(pool_path), parent, F(parent["r_strict_interval"][1]))
    if len(receipts) != 215 or len(binding.read(pool_path)) != 87:
        raise ValueError("six-target source geometry lost an old type or proof receipt")
    negatives = []
    def rejected(name, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(name)
        else:
            raise AssertionError("invalid six-target whole-geometry scope accepted: "+name)
    changed = deepcopy(binding.read(folder/"SOURCE-FINAL.json"))
    changed["all_current_file_digests_rehashed"] = False
    rejected("unverified-actual-parent-final", lambda: previous.parent_gate(
        parent, changed, manifest["parent_current_sha256"]))
    changed_constants = dict(constants, minimum_interior_cells=8)
    rejected("missing-original-nonowner-family-bound", lambda: transfer.rule.family_gate(changed_constants))
    changed_certificates = deepcopy(certificates)
    changed_certificates["bridge"]["explicit_ordered_real_hypotheses"].pop()
    rejected("shadow-nearest-cell-frame-substitution", lambda: transfer.lemma_gate(changed_certificates, proofs))
    changed_proofs = dict(proofs)
    changed_proofs.pop("six")
    rejected("continuous-six-target-proof-not-bound", lambda: transfer.lemma_gate(certificates, changed_proofs))
    rejected("six-target-radius-scope-promoted", lambda: transfer.rule.target_gate(u=F(1, 4)))
    def case_record_gate(record):
        expected = transfer.independent.independent_original_cases(
            record["actual_entire_source_state"], record["selected_strongest_filled_patch"])
        if record["all_original_physical_count_and_shadow_case_distributions"] != expected:
            raise ValueError("an original count/shadow case is missing or changed")
    changed_record = deepcopy(ledger[0])
    changed_record["all_original_physical_count_and_shadow_case_distributions"].pop()
    rejected("missing-original-physical-count-case", lambda: case_record_gate(changed_record))
    extra_paths = [
        folder/"MANIFEST.json", *(folder/name for name in manifest["copied_files"]),
        binding.local_path(manifest["parent_current"]), binding.local_path(manifest["parent_final"]),
        *family_paths, *provenance_paths,
    ]
    for path in extra_paths:
        text, digest = linux(path), binding.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("six-target parent/supplement inventories disagree")
        inventory[text] = digest
    print("Rehashing ENTIRE parent+SIX-target proof/source/control inventory after semantics.", flush=True)
    previous.rehash(inventory, "six-target-after-semantic-replay")
    new_manifest, new_parent, new_source, new_layer = input_gate(folder)
    if (
        binding.sha(folder/"MANIFEST.json") != manifest_digest or new_manifest != manifest
        or new_parent != parent or new_source != source or new_layer != layer
    ):
        raise ValueError("six-target actual source/current/candidate identity changed during the full main")
    report = {
        "schema": SCHEMA, "verified": True, "radius_scope": binding.SCOPE,
        "radius_upper": source["radius_upper"], "r_strict_interval": parent["r_strict_interval"],
        "screen_radius_threshold_for_NEW_six_target_rule": str(transfer.U),
        "inherited_source_is_unconditional_at_U": False,
        "executed_checker_file": CHECKER, "executed_checker_sha256": manifest["copied_files"][CHECKER],
        "actual_parent_current_sha256": manifest["parent_current_sha256"],
        "actual_parent_final_sha256": manifest["parent_final_sha256"],
        "actual_source_frontier_sha256": manifest["source_frontier_sha256"],
        "actual_candidate_layer_identity": layer,
        "complete_parent_dependency_inventory_rehashed_BEFORE_AND_AFTER": True,
        "prior_completed_parent_semantic_proof_chain_still_bound_NOT_replaced_by_DATA": True,
        "actual_original_owner_family_theorem_rechecked_with_EXPLICIT_imported_n8": family_result,
        "ENTIRE_actual_source_prefixes_six_target_geometry_and_case_partition_replayed_here": semantic,
        "fresh_independent_universal_bridge_scalar_identities": independent_symbols,
        "historical_closed_types_retained": 87, "historical_proof_receipts_retained_and_associated": 215,
        "all_original_candidate_terminals_owned_roots_histories_and_LOCAL_retained": True,
        "source_actual_current_frontier": len(source["pending_states"]),
        "geometry_accepted_filtered_frontier_REQUIRES_CURRENT_AND_FINAL": len(frontier["pending_states"]),
        "strict_new_six_target_whole_source_prefixes": len(ledger),
        "all_original_counts_AND_shadow_label_placements_freshly_checked_both_ways": True,
        "corner_shadow_is_embedded_LIMIT_NOT_26_positive_area_Voronoi_cells": True,
        "written_continuous_cover_embedding_and_six_target_proofs_used_NOT_inferred_from_finite_tests": True,
        "old643_scope_NOT_used_as_acceptance_of_additional4903": True,
        "actual_geometric_scope_negative_controls_rejected": negatives,
        "actual_current_nodes_removed_by_this_OWN_acceptance": 0,
        "new_formal_geometric_payments_by_this_OWN_acceptance": 0,
        "candidate_whole_roots_removed": 0, "original_U_frontier_nodes_removed": 0,
        "unrestricted_reduction_final_joint_acceptance": False, "frozen_geometric_reduction_proved": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {**manifest["copied_files"], "MANIFEST.json": manifest_digest},
        "source_files": inventory,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_entire_source_SIX_target_geometry_main_completed": True,
        "whole_prefixes": len(ledger), "filtered_frontier_NOT_yet_current": len(frontier["pending_states"]),
        "current_AND_independent_final_STILL_required": True, "candidate_whole_roots_removed": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
