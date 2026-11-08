"""REAL entire remaining-source main for NEW680 midarc geometric exclusions.

Own, publication and subsequent current semantics must run this same frozen
main. No cached/fast/skip acceptance. Parent is the ACTUAL completed
mixed-after-SIX16-root pair; no synthetic header or old25-root replacement.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import sys

from audit_prefix_partition import linux
import audit_stage_catalogue_with_closed_pool as historical
import n26_candidate_identity_after_six_target as identity
import n26_midarc_cover_transfer as transfer
import n26_midarc_source_accounting as accounting
import test_embedded_dual_bridge_algebra as independent_bridge
import verify_closed_ear_source_geometry as previous
import verify_conditional_force_stage as binding


INPUT_SCHEMA = accounting.INPUT_SCHEMA
SCHEMA = accounting.ACCEPTANCE_SCHEMA
CHECKER = accounting.CHECKER
PROOFS = {**previous.PROOFS, "midarc": "MIDARC-SEVEN-SIX-FIVE-TARGET-PROOF.md"}
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
    manifest = binding.read(folder / "MANIFEST.json")
    if (
        manifest["schema"] != INPUT_SCHEMA or manifest["checker"] != CHECKER
        or manifest["rule_mode"] != transfer.MODE or manifest["radius_scope"] != accounting.SCOPE
        or manifest["full_actual_parent_inventory_and_source_reconstruction_required"] is not True
        or manifest["current_adoption_is_not_done_by_own_geometry"] is not True
        or manifest["only_actual_remaining680_NOT_repaying_old5546"] is not True
        or manifest["actual_mixed16root_owner_and_newest_histories_REQUIRED"] is not True
    ):
        raise ValueError("midarc geometry changed its entire-source/original-owner admission scope")
    for name, digest in manifest["copied_files"].items():
        if binding.sha(folder / name) != digest:
            raise ValueError("midarc frozen input changed: " + name)
    for name, path in executed_modules().items():
        if manifest["copied_files"].get(name) != binding.sha(path):
            raise ValueError("midarc loaded execution module differs from its frozen copy: " + name)
    parent_path, final_path = (
        binding.local_path(manifest[field]) for field in ("parent_current", "parent_final")
    )
    source_path = binding.local_path(manifest["source_frontier"])
    acceptance_path = binding.local_path(manifest["source_acceptance"])
    for path, digest in (
        (parent_path, manifest["parent_current_sha256"]),
        (final_path, manifest["parent_final_sha256"]),
        (source_path, manifest["source_frontier_sha256"]),
        (acceptance_path, manifest["source_acceptance_sha256"]),
    ):
        if binding.sha(path) != digest:
            raise ValueError("midarc actual completed parent/source bytes changed")
    parent, final = binding.read(folder / "SOURCE-CURRENT.json"), binding.read(folder / "SOURCE-FINAL.json")
    if parent != binding.read(parent_path) or final != binding.read(final_path):
        raise ValueError("midarc substituted the ACTUAL completed mixed-after-SIX current/final")
    accounting.parent_gate(parent, final, manifest["parent_current_sha256"])
    expected_final_path = binding.local_path(manifest["actual_parent_final_executor"])
    if (
        expected_final_path.name != "recheck_mixed_curvature_candidate_after_six_current.py"
        or final["executed_checker_sha256"] != binding.sha(expected_final_path)
        or parent["files"].get(linux(expected_final_path)) != binding.sha(expected_final_path)
    ):
        raise ValueError("midarc parent lacks the bound actual independent mixed-after-SIX final executor")
    source = binding.read(folder / "SOURCE-FRONTIER.json")
    accepted = binding.read(folder / "SOURCE-ACCEPTANCE.json")
    if (
        source != binding.read(source_path) or accepted != binding.read(acceptance_path)
        or parent["current_frontier_actual_file"] != linux(source_path)
        or parent["files"].get(linux(source_path)) != manifest["source_frontier_sha256"]
        or parent["files"].get(linux(acceptance_path)) != manifest["source_acceptance_sha256"]
        or accepted["schema"] != "N26-actual-whole-source-six-target-filled-ear-geometry-acceptance-v1"
        or accepted["verified"] is not True
        or accepted["files"]["FRONTIER.json"] != manifest["source_frontier_sha256"]
        or source["schema"] != accounting.SOURCE_SCHEMA
        or len(source["pending_states"]) != 5637
        or source["families"] != parent["Rstar_conditional_frontier_families"]
        or source["radius_scope"] != accounting.SCOPE
        or F(source["radius_upper"]) != F(parent["r_strict_interval"][1])
    ):
        raise ValueError("midarc source is not the actual retained SIX-filtered parent frontier")
    candidate = binding.local_path(manifest["actual_candidate_source"])
    publication_path = binding.local_path(manifest["actual_candidate_publication"])
    layer = identity.gate(parent, manifest["parent_current_sha256"], candidate)
    if (
        layer["actual_remaining_candidate_whole_roots"] != 16
        or binding.read(candidate / "VERIFIED.json") != binding.read(publication_path)
        or parent["files"].get(linux(publication_path)) != binding.sha(publication_path)
        or parent["actual_current_candidate_remaining_history"] != linux(
            candidate / "REMAINING-ROOT-HISTORY.json")
        or parent["files"].get(linux(candidate / "REMAINING-ROOT-HISTORY.json"))
        != binding.sha(candidate / "REMAINING-ROOT-HISTORY.json")
    ):
        raise ValueError("midarc geometry reset actual candidate ownership or latest partial histories")
    return manifest, parent, source, layer


def controls_gate(folder, source, manifest):
    producer = binding.read(folder / "MIDARC-MATHEMATICAL-SCAN.json")
    independent = binding.read(folder / "MIDARC-INDEPENDENT-CONTROLS.json")
    remaining = binding.read(folder / "REMAINING-SOURCE-ACCOUNTING-CONTROLS.json")
    if (
        any(record["verified"] is not False for record in (producer, independent, remaining))
        or any(record["new_formal_geometric_payments"] != 0 for record in (
            producer, independent, remaining))
        or producer["qualifying_whole_prefixes"] != 6226
        or independent["independent_qualifying_whole_prefixes"] != 6226
        or independent["entire_original_source_prefixes_independently_reconstructed"] != 11183
        or independent["independent_all_original_count_AND_shadow_label_cases_checked"] != 68088
        or independent["additional_beyond_frozen_six_triangles_NOT_admitted"] != 680
        or len(independent["topology_and_strict_target_negative_controls_rejected"]) != 11
        or remaining["schema"] != "N26-midarc-SIX-filtered-source-independent-accounting-controls-v1"
        or remaining["entire_actual5637_ORIGINAL_prefixes_freshly_reconstructed"] is not True
        or remaining["only_remaining680_paid_NOT_old5546_repaid"] is not True
        or remaining["actual_SIX_geometry_DATA_not_claimed_a_completed_current_parent"] is not True
        or remaining["synthetic_parent_final_headers_NOT_geometry_or_current_acceptance"] is not True
        or remaining["actual_SIX_filtered_frontier_sha256"] != manifest["source_frontier_sha256"]
        or remaining["tested_transfer_sha256"] != binding.sha(transfer.__file__)
        or remaining["tested_accounting_sha256"] != binding.sha(accounting.__file__)
        or remaining["executed_test_sha256"] != binding.sha(
            Path(__file__).with_name("test_midarc_SIX_filtered_source_accounting.py"))
        or len(remaining["invalid_controls_rejected"]) != 21
        or remaining["actual_independent_NEW680_source_partition"]["retained_unpaid_source_prefixes"] != 4957
        or len(source["pending_states"]) != 5637
    ):
        raise ValueError("midarc geometry lacks actual full11183 and remaining5637 independent controls")
    for name, field in (
        ("MIDARC-MATHEMATICAL-SCAN.json", "mathematical_scan_sha256"),
        ("MIDARC-INDEPENDENT-CONTROLS.json", "independent_controls_sha256"),
        ("REMAINING-SOURCE-ACCOUNTING-CONTROLS.json", "remaining_source_controls_sha256"),
    ):
        if binding.sha(folder / name) != manifest[field]:
            raise ValueError("midarc frozen control result changed")
    paths = []
    for record in (producer, independent, remaining):
        for text, digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("midarc actual source/control provenance changed: " + text)
            paths.append(binding.local_path(text))
    return paths


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("preserve midarc own/publication/partial outputs; never repeat a completed main")
    folder = args.input
    manifest, parent, source, layer = input_gate(folder)
    manifest_digest = binding.sha(folder / "MANIFEST.json")
    inventory = dict(parent["files"])
    print("Rehashing EVERY actual completed mixed-after-SIX dependency before NEW midarc geometry.",
          flush=True)
    previous.rehash(inventory, "midarc-before-semantic-replay")
    constants, family_result, family_paths = previous.family_gate(folder, manifest, parent)
    provenance_paths = controls_gate(folder, source, manifest)
    certificates = {key: binding.read(folder / name) for key, name in CERTIFICATES.items()}
    proofs = {key: binding.sha(folder / name) for key, name in PROOFS.items()}
    independent_symbols = independent_bridge.independent_identities(certificates["bridge"])
    if independent_symbols != 12:
        raise ValueError("midarc geometry lacks fresh independent universal bridge identities")
    print("Reconstructing ALL5637 ORIGINAL source prefixes and NEW680 whole-patch label cases.",
          flush=True)
    frontier, ledger, semantic = transfer.partition(source, constants, certificates, proofs)
    independent_partition = accounting.partition_gate(source, frontier, ledger, constants, proofs)
    remaining_controls = binding.read(folder / "REMAINING-SOURCE-ACCOUNTING-CONTROLS.json")
    if (
        frontier != binding.read(folder / "FRONTIER.json")
        or ledger != binding.read(folder / "LOWER-LEDGER.json")
        or semantic != binding.read(folder / "SOURCE-MATHEMATICAL-SEMANTICS.json")
        or independent_partition != remaining_controls["actual_independent_NEW680_source_partition"]
    ):
        raise ValueError("midarc ENTIRE source/independent accounting did not freshly reconstruct")
    pool_path = binding.local_path(manifest["closed_type_pool"])
    receipt_path = binding.local_path(manifest["closed_receipt_checks"])
    terminal_path = binding.local_path(manifest["terminal_obligations"])
    for path in (pool_path, receipt_path, terminal_path):
        if parent["files"].get(linux(path)) != binding.sha(path):
            raise ValueError("midarc source lost historical type/receipt/raw terminal ownership")
    receipts = historical.retained_pool_gate(
        binding.read(pool_path), parent, F(parent["r_strict_interval"][1]),
    )
    if len(receipts) != 215 or len(binding.read(pool_path)) != 87 or binding.read(receipt_path) != receipts:
        raise ValueError("midarc source lost an actual original proof receipt/type classification")
    negative = []

    def reject(name, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(name)
        else:
            raise AssertionError("invalid midarc actual geometry scope accepted: " + name)

    changed_final = deepcopy(binding.read(folder / "SOURCE-FINAL.json"))
    changed_final["all_current_file_digests_rehashed"] = False
    reject("unverified-actual-mixed-parent-final", lambda: accounting.parent_gate(
        parent, changed_final, manifest["parent_current_sha256"]))
    changed_parent = deepcopy(parent)
    changed_parent["candidate_angle_unresolved_closed_boxes"] = 25
    reject("older25root-candidate-owner-restored", lambda: accounting.parent_gate(
        changed_parent, binding.read(folder / "SOURCE-FINAL.json"), manifest["parent_current_sha256"]))
    changed_constants = dict(constants, minimum_interior_cells=8)
    reject("missing-original-nonowner-family-bound", lambda: transfer.family.family_gate(changed_constants))
    changed_certificates = deepcopy(certificates)
    changed_certificates["bridge"]["explicit_ordered_real_hypotheses"].pop()
    reject("shadow-nearest-cell-frame-substitution", lambda: transfer.lemma_gate(
        changed_certificates, proofs))
    changed_proofs = dict(proofs)
    changed_proofs.pop("midarc")
    reject("continuous-midarc-proof-not-bound", lambda: transfer.lemma_gate(certificates, changed_proofs))
    reject("quarter-radius-nonstrict-target-scope", lambda: transfer.rule.target_gate(3, u=F(1, 4)))

    def record_gate(record):
        expected = accounting.independent_original_cases(
            record["actual_entire_source_state"], record["selected_strongest_filled_patch"])
        if record["all_original_physical_count_and_shadow_case_distributions"] != expected:
            raise ValueError("midarc original physical count/shadow case changed")

    changed_record = deepcopy(ledger[0])
    changed_record["all_original_physical_count_and_shadow_case_distributions"].pop()
    reject("missing-original-physical-count-case", lambda: record_gate(changed_record))
    changed_ledger = [*ledger, ledger[0]]
    reject("duplicate-whole-prefix-payment", lambda: accounting.partition_gate(
        source, frontier, changed_ledger, constants, proofs))
    changed_source = dict(source, radius_scope="unconditional-original-U")
    reject("conditional-source-promoted-to-original-U", lambda: accounting.partition_gate(
        changed_source, frontier, ledger, constants, proofs))
    changed_source = dict(source, pending_states=[*source["pending_states"], source["pending_states"][0]])
    reject("old-paid-prefix-reopened-as-extra-source", lambda: accounting.partition_gate(
        changed_source, frontier, ledger, constants, proofs))
    if len(negative) != 10:
        raise AssertionError("midarc actual geometry scope controls incomplete")
    paths = [
        folder / "MANIFEST.json", *(folder / name for name in manifest["copied_files"]),
        binding.local_path(manifest["parent_current"]), binding.local_path(manifest["parent_final"]),
        binding.local_path(manifest["actual_candidate_publication"]),
        *family_paths, *provenance_paths,
    ]
    for path in paths:
        text, digest = linux(path), binding.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("midarc inherited and new proof inventories disagree")
        inventory[text] = digest
    print("Rehashing ENTIRE mixed/SIX+NEW midarc inventory after complete semantic execution.", flush=True)
    previous.rehash(inventory, "midarc-after-semantic-replay")
    latest_manifest, latest_parent, latest_source, latest_layer = input_gate(folder)
    if (
        binding.sha(folder / "MANIFEST.json") != manifest_digest or latest_manifest != manifest
        or latest_parent != parent or latest_source != source or latest_layer != layer
    ):
        raise ValueError("midarc actual source/latest candidate/parent changed during complete main")
    report = {
        "schema": SCHEMA, "verified": True, "radius_scope": accounting.SCOPE,
        "radius_upper": source["radius_upper"], "r_strict_interval": parent["r_strict_interval"],
        "screen_radius_threshold_for_NEW_midarc_rule": str(transfer.U),
        "inherited_source_is_unconditional_at_U": False,
        "executed_checker_file": CHECKER, "executed_checker_sha256": manifest["copied_files"][CHECKER],
        "actual_parent_current_sha256": manifest["parent_current_sha256"],
        "actual_parent_final_sha256": manifest["parent_final_sha256"],
        "actual_source_frontier_sha256": manifest["source_frontier_sha256"],
        "actual_candidate_layer_identity": layer,
        "complete_parent_dependency_inventory_rehashed_BEFORE_AND_AFTER": True,
        "prior_completed_parent_semantic_proof_chain_still_bound_NOT_replaced_by_DATA": True,
        "actual_original_owner_family_theorem_rechecked_with_EXPLICIT_imported_n8": family_result,
        "ENTIRE_actual_source_prefixes_midarc_geometry_and_case_partition_replayed_here": semantic,
        "independent_complete_actual_remaining_source_accounting": independent_partition,
        "fresh_independent_universal_bridge_scalar_identities": independent_symbols,
        "historical_closed_types_retained": 87, "historical_proof_receipts_retained_and_associated": 215,
        "all_actual16_candidate_roots_histories_and_original_LOCAL_retained": True,
        "source_actual_current_frontier": 5637,
        "geometry_accepted_filtered_frontier_REQUIRES_CURRENT_AND_FINAL": 4957,
        "strict_NEW_midarc_whole_source_prefixes": 680,
        "old5546_SIX_whole_prefix_payments_preserved_NOT_repaid": True,
        "all_original_counts_AND_shadow_label_placements_freshly_checked_both_ways": True,
        "corner_shadow_is_embedded_LIMIT_NOT26_positive_area_Voronoi_cells": True,
        "written_continuous_midarc_cover_and_embedding_proofs_used_NOT_inferred_from_finite_tests": True,
        "actual_geometric_scope_negative_controls_rejected": negative,
        "actual_current_nodes_removed_by_this_OWN_acceptance": 0,
        "new_formal_geometric_payments_by_this_OWN_acceptance": 0,
        "candidate_whole_roots_removed": 0, "original_U_frontier_nodes_removed": 0,
        "unrestricted_reduction_final_joint_acceptance": False, "frozen_geometric_reduction_proved": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {**manifest["copied_files"], "MANIFEST.json": manifest_digest},
        "source_files": inventory,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "actual_ENTIRE_remaining_source_midarc_geometry_main_completed": True,
        "NEW_whole_prefixes": 680, "filtered_frontier_NOT_yet_current": 4957,
        "actual16_candidate_roots_retained": True, "current_AND_independent_final_STILL_required": True,
        "candidate_whole_roots_removed": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
