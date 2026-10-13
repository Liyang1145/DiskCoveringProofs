"""Independent FULL current-content final for imported N25 SOURCE premises.

Separate streaming file hashing. Prior mathematics is reused honestly.
This is not an N26 graph/current/global-optimality acceptance.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import sys

import n26_import_n25_source_common as prior


def local_path(value):
    text = str(value).replace("\\", "/")
    if sys.platform == "win32" and text.startswith("/mnt/"):
        return Path(text[5].upper()+":"+text[6:])
    if sys.platform != "win32" and len(text) > 2 and text[1] == ":":
        return Path("/mnt/"+text[0].lower()+text[2:])
    return Path(text)


def sha(path):
    value = hashlib.sha256()
    with local_path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(2*1024*1024), b""):
            value.update(block)
    return value.hexdigest()


def read(path):
    return json.loads(local_path(path).read_text(encoding="utf-8"),
                      object_pairs_hook=prior.unique_object)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--import", dest="import_folder", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError("prior-source independent final never overwrites an existing report")
    own_path = args.import_folder/"VERIFIED.json"
    initial = sha(own_path)
    own = read(own_path)
    if (
        own["schema"] != "N26-qualified-imported-N25-source-and-exact-original-cardinality-admission-v1"
        or own["verified"] is not True
        or own["all555483_actual_prior_prerequisite_files_and_whole_archives_freshly_rehashed"] is not True
        or own["prior_dependency_count"] != 555483
        or own["all721329_prior_parent_statuses_partitioned_and_zero_pending"] is not True
        or own["prior_binding_creator_terminal_missing_qualification_preserved"] is not True
        or own["prior_SOURCEmathematics_reused_NOT_claimed_new_full_tree_replays"] is not True
        or own["byte_content_checks_NOT_claimed_machine_proof_of_written_geometry"] is not True
        or own["prior_proof_scope_NOT_Lean_Coq_or_third_party_peer_review"] is not True
        or own["not_an_N26_current_audit_or_graph_geometry_acceptance"] is not True
        or own["new_formal_geometric_payments"] != 0
        or any(own[field] is not False for field in (
            "global_lower_bound_proved", "global_optimality_proved", "n27_started"))
        or own["actual_prior_N25_accepted_source_sha256"] != prior.EXPECTED["accepted"]
        or own["actual_prior_whole_prerequisite_binding_sha256"] != prior.EXPECTED["binding"]
        or own["actual_prior_frozen_input_ledger_sha256"] != prior.EXPECTED["ledger"]
    ):
        raise ValueError("imported prior-source final changed its qualified proof/content-only scope")
    for path, digest in (
        (prior.SOURCE, prior.EXPECTED["accepted"]), (prior.BINDING, prior.EXPECTED["binding"]),
        (prior.LEDGER, prior.EXPECTED["ledger"]), (prior.FROZEN_LEDGER, prior.EXPECTED["ledger"]),
    ):
        if sha(path) != digest:
            raise ValueError("actual imported old source/complete prerequisite snapshot changed")
    accepted, binding = read(prior.SOURCE), read(prior.BINDING)
    implication = prior.scope_gate(accepted, binding)
    if implication != own["exact_original_cardinality_implication_under_imported_prior_theorem"]:
        raise ValueError("independent exact radical/cardinality implication differs")
    code_paths = [local_path(text) for text in own["helper_and_proof_bindings"]]
    for text, digest in own["helper_and_proof_bindings"].items():
        if sha(text) != digest:
            raise ValueError("an actual importer/scope/proof/control input changed")
    if (
        own["executed_checker_sha256"] != sha(Path(__file__).with_name("verify_imported_n25_source_for_n26.py"))
        or own["executed_scope_and_collection_helper_sha256"] != sha(prior.__file__)
        or str(Path(__file__).resolve()) not in own["helper_and_proof_bindings"]
    ):
        raise ValueError("import independent final or actual executed primary/helper was not bound")
    expected, old_count = prior.collect_prior_inventory(accepted, code_paths)
    ledger_path = args.import_folder/"IMPORTED-INPUTS.jsonl"
    if (
        local_path(own["imported_input_ledger"]).resolve() != ledger_path.resolve()
        or sha(ledger_path) != own["imported_input_ledger_sha256"]
        or len(expected) != own["full_imported_dependency_count"]
    ):
        raise ValueError("actual full imported input ledger or count changed")
    seen, previous, count = set(), None, 0
    with ledger_path.open(encoding="ascii") as stream:
        for count, line in enumerate(stream, 1):
            row = json.loads(line, object_pairs_hook=prior.unique_object)
            if set(row) != {"path", "sha256"}:
                raise ValueError("invalid actual imported dependency row")
            text, digest = row["path"], row["sha256"]
            normalized = os.path.normpath(os.path.abspath(str(local_path(text))))
            key = normalized.casefold() if sys.platform == "win32" else normalized
            if (
                key in seen or expected.get(normalized) != digest
                or (previous is not None and previous >= text)
            ):
                raise ValueError("import final detected omitted, repeated, reordered or substituted inputs")
            seen.add(key)
            previous = text
            if sha(text) != digest:
                raise ValueError("independent imported N25 source content changed: "+text)
            if count % 10000 == 0:
                print(json.dumps({"independent_imported_N25_dependencies_rehashed": count,
                                  "total": len(expected)}), flush=True)
    if count != len(expected):
        raise ValueError("import final did not cover every original prerequisite and extra binding")
    families = prior.family_ledger_gate(accepted)
    if families != own["all_four_actual_parent_ledgers_freshly_sequentially_checked"]:
        raise ValueError("fresh whole-parent N25 partitions differ from primary import")
    for text, digest in {
        **own["helper_and_proof_bindings"], **accepted["new_global_entry_frozen_files"],
        str(prior.SOURCE): prior.EXPECTED["accepted"], str(prior.BINDING): prior.EXPECTED["binding"],
        str(prior.LEDGER): prior.EXPECTED["ledger"], str(prior.FROZEN_LEDGER): prior.EXPECTED["ledger"],
    }.items():
        if sha(text) != digest:
            raise ValueError("import final source/closure/executor changed during the independent audit")
    if sha(own_path) != initial or sha(ledger_path) != own["imported_input_ledger_sha256"]:
        raise ValueError("actual prior-source import admission/complete input ledger changed during final")
    report = {
        "schema": "N26-independent-qualified-N25-source-import-final-v1",
        "verified": True, "import_own_acceptance_sha256": initial,
        "imported_input_ledger_sha256": own["imported_input_ledger_sha256"],
        "all_actual_imported_dependency_content_independently_rehashed": True,
        "actual_original_N25_prerequisite_count": old_count,
        "actual_full_imported_dependency_count": count,
        "all_four_actual_N25_parent_payment_ledgers_freshly_checked": families,
        "exact_original_cardinality_implication_under_imported_prior_theorem": implication,
        "imported_theorem_scope_is_qualified_prior_SOURCE_NOT_a_new_old_tree_replay": True,
        "original_missing_binding_creator_terminal_qualification_preserved": True,
        "not_N26_global_or_graph_current_acceptance": True,
        "N26_joint_source_geometry_current_AND_final_still_required": True,
        "new_formal_geometric_payments": 0, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "executed_checker_sha256": sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_independent_FULL_prior_SOURCE_import_final_completed": True,
        "prior_prerequisites": old_count, "all_imported_dependencies": count,
        "original_physical_disks_in_scope_under_imported_prior_theorem": 26,
        "N26_global_optimality_proved": False,
    }), flush=True)


if __name__ == "__main__":
    main()
