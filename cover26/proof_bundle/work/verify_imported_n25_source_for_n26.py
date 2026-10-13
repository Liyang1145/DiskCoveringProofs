"""Fresh full prior-proof content admission, not a new replay of old N25 math."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

import n26_import_n25_source_common as prior


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError("prior-proof importer never resets a completed or partial output")
    for path, expected in (
        (prior.SOURCE, prior.EXPECTED["accepted"]), (prior.BINDING, prior.EXPECTED["binding"]),
        (prior.LEDGER, prior.EXPECTED["ledger"]), (prior.FROZEN_LEDGER, prior.EXPECTED["ledger"]),
    ):
        if prior.sha(path) != expected:
            raise ValueError("actual qualified accepted N25 source/complete premise snapshot changed")
    accepted, binding = prior.read(prior.SOURCE), prior.read(prior.BINDING)
    implication = prior.scope_gate(accepted, binding)
    controls_path = Path("outputs/n26-imported-n25-exactly26-original-cardinality-mathematical-controls-v1.json")
    controls = prior.read(controls_path)
    proof_path = Path("work/n26-exactly26-original-disks-from-imported-n25-proof.md")
    if (
        controls["verified"] is not False or controls["new_formal_geometric_payments"] != 0
        or controls["actual_imported_n25_source_entry_sha256"] != prior.EXPECTED["accepted"]
        or controls["written_implication_proof_sha256"] != prior.sha(proof_path)
        or controls["executed_test_sha256"] != prior.sha(Path("work/test_n25_import_for_n26_physical_cardinality.py"))
        or len(controls["actual_invalid_import_scope_and_radius_controls_rejected"]) != 9
        or controls["actual_n25_ENTIRE_prerequisite_content_rehash_NOT_performed_here"] is not True
    ):
        raise ValueError("actual prior-theorem implication controls do not match their limited scope")
    families = prior.family_ledger_gate(accepted)
    negative = []
    for name, field, value in (
        ("unfinished-prior-SOURCE-theorem", "global_source_proof_closed", False),
        ("missing-whole-family", "required_boundary_families", [14, 15, 16]),
        ("fewer-disks-scope-hidden", "arbitrary_plane_centers_repetitions_fewer_disks_and_degeneracies_allowed", False),
        ("old-trees-falsely-claimed-newly-replayed", "all_old_exact_mathematics_honestly_reused_not_new_full_all_old_tree_replays", False),
        ("written-math-falsely-machine-proved-by-hashes", "written_math_not_claimed_machine_proved_by_content_check", False),
    ):
        changed = deepcopy(accepted)
        changed[field] = value
        try:
            prior.scope_gate(changed, binding)
        except (ValueError, KeyError, TypeError):
            negative.append(name)
        else:
            raise AssertionError("invalid imported proof scope accepted: "+name)
    extra_files = [
        Path(__file__), Path(prior.__file__), proof_path, controls_path,
        Path("work/test_n25_import_for_n26_physical_cardinality.py"),
        Path("work/recheck_imported_n25_source_for_n26.py"),
    ]
    inventory, old_count = prior.collect_prior_inventory(accepted, extra_files)
    code_digests = {str(path.resolve()): prior.sha(path) for path in extra_files}
    args.output.mkdir(parents=True)
    ledger_path = args.output/"IMPORTED-INPUTS.jsonl"
    print("Rehashing ALL actual imported N25 prerequisite files and whole archives.", flush=True)
    with ledger_path.open("x", encoding="ascii", newline="\n") as target:
        for number, text in enumerate(sorted(inventory), 1):
            if prior.sha(text) != inventory[text]:
                raise ValueError("imported N25 current prerequisite content changed: "+text)
            target.write(json.dumps({"path": text, "sha256": inventory[text]}, separators=(",", ":"))+"\n")
            if number % 10000 == 0:
                print(json.dumps({"imported_N25_actual_dependency_content_rehashed": number,
                                  "total": len(inventory)}), flush=True)
    for text, digest in {
        **accepted["new_global_entry_frozen_files"], **code_digests,
        str(prior.SOURCE): prior.EXPECTED["accepted"], str(prior.BINDING): prior.EXPECTED["binding"],
        str(prior.LEDGER): prior.EXPECTED["ledger"], str(prior.FROZEN_LEDGER): prior.EXPECTED["ledger"],
    }.items():
        if prior.sha(text) != digest:
            raise ValueError("imported source/closure/executor changed during full current content binding")
    report = {
        "schema": "N26-qualified-imported-N25-source-and-exact-original-cardinality-admission-v1",
        "verified": True,
        "actual_prior_N25_accepted_source": str(prior.SOURCE),
        "actual_prior_N25_accepted_source_sha256": prior.EXPECTED["accepted"],
        "actual_prior_whole_prerequisite_binding": str(prior.BINDING),
        "actual_prior_whole_prerequisite_binding_sha256": prior.EXPECTED["binding"],
        "actual_prior_frozen_input_ledger_sha256": prior.EXPECTED["ledger"],
        "all555483_actual_prior_prerequisite_files_and_whole_archives_freshly_rehashed": True,
        "prior_dependency_count": old_count, "full_imported_dependency_count": len(inventory),
        "all_four_actual_parent_ledgers_freshly_sequentially_checked": families,
        "all721329_prior_parent_statuses_partitioned_and_zero_pending": True,
        "prior_binding_creator_terminal_missing_qualification_preserved": True,
        "prior_SOURCEmathematics_reused_NOT_claimed_new_full_tree_replays": True,
        "byte_content_checks_NOT_claimed_machine_proof_of_written_geometry": True,
        "prior_proof_scope_NOT_Lean_Coq_or_third_party_peer_review": True,
        "exact_original_cardinality_implication_under_imported_prior_theorem": implication,
        "invalid_imported_proof_scope_controls_rejected": negative,
        "imported_input_ledger": str(ledger_path.resolve()),
        "imported_input_ledger_sha256": prior.sha(ledger_path),
        "executed_checker_sha256": prior.sha(__file__),
        "executed_scope_and_collection_helper_sha256": prior.sha(prior.__file__),
        "helper_and_proof_bindings": code_digests,
        "independent_full_import_final_STILL_required": True,
        "not_an_N26_current_audit_or_graph_geometry_acceptance": True,
        "new_formal_geometric_payments": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with (args.output/"VERIFIED.json").open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_full_prior_N25_content_import_admission_completed": True,
        "prior_prerequisites": old_count, "all_imported_dependencies": len(inventory),
        "all_parent_statuses": sum(item["whole_parent_rows_freshly_checked"] for item in families),
        "independent_full_import_final_STILL_required": True, "N26_global_optimality_proved": False,
    }), flush=True)


if __name__ == "__main__":
    main()
