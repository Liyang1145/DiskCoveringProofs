"""Full N25 source/lower/radical/core content closure, only after real B17 zero."""
from pathlib import Path
from collections import Counter, deque
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
WORK = ROOT.parents[2]
INCOMING = ROOT.parents[4]
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish

assert __debug__
SOURCEPATH = ROOT / "n25-four-actual-complete-source-interfaces-v1/VERIFIED.json"
COREPATH = ROOT / "n25-own-exact-upper-endpoint-full-core-interface-v1/VERIFIED.json"
BUDGETPATH = ROOT / "n25-own-exact-family-budget-v1/VERIFIED.json"
DOCUMENT = ROOT / "N25-GLOBAL-SOURCE-PROOF-v1.md"
FINALPATHS = {
    14: ROOT / "n25-B14-all-parent-lower-chain-audit-20261005-v1/VERIFIED.json",
    15: ROOT / "n25-B15-final15-full-parent-finer-and-direct-audit-solo-v1/VERIFIED.json",
    16: ROOT / "n25-B16-final1/ACCEPTED/VERIFIED.json",
    17: ROOT / "n25-B17-final1/ACCEPTED/VERIFIED.json",
}
TOTALS = {14: 172092, 15: 139315, 16: 120782, 17: 289140}


def interface_gate(source, core, budget):
    assert source["verified"] and source["N"] == 25
    assert source["schema"] == "N25-four-actual-complete-necessary-sources-and-all-nonzero-strict-library-guards-v1"
    assert source["source_sha256"] == sha(ROOT / "verify_n25_complete_source_interfaces.py")
    assert source["necessary_boundary_internal_families"] == [[b, 25-b] for b in range(14, 18)]
    assert source["complete_necessary_residual_weak_graph_counts"] == list(TOTALS.values())
    assert source["total_necessary_residual_weak_graphs"] == 721329
    for key in (
        "actual_223_loaded_strict_library_trees_fresh_exactly_mathematically_reaccepted",
        "all_selected_actual_nonzero_pruning_uses_fully_validated_injection_on_each_positive_return",
        "correct_B14_origin_later_payment_and_B15_degree_upper_and_B15_B16_candidate_cache_scopes",
        "old_full_enumerations_and_exact_unions_honestly_reused_not_claimed_new_large_runs",
        "written_cover_full_peeling_omission_and_positive_guard_transport_reviewed_math_premises"):
        assert source[key]
    assert core["verified"] and core["N"] == 25
    assert core["schema"] == "N25-own-radical-exact-upper-fresh-endpoint-local-and-real-full-core-interface-v1"
    assert core["source_sha256"] == sha(ROOT / "verify_n25_exact_upper_endpoint_interface.py")
    assert core["exact_radius"] == "1/(sqrt(6)+sqrt(3))"
    assert core["exact_radius_squared_Qsqrt2"] == ["1", "-2/3"]
    for key in (
        "same_exact_radius_not_approximate_decimal_or_other_order",
        "all_actual25_disk_closed_unit_disk_upper_freshly_exactly_recomputed",
        "both120_endpoint_local_principal_minors_and_perturbation_margins_freshly_recomputed",
        "fresh_local_report_identical_to_original_entire_angle_theorem_local_premise",
        "actual_full91_family_and_unique_full_core_all_center_anchor_and_face_maps_rechecked",
        "specified311883_node_entire_core_math_honestly_reused_unchanged_not_claimed_new_replay",
        "specified_core_lower_nonstrict_R_not_strict_U_and_not_all_competing_graphs",
        "full288_variable_KKT_root_not_claimed_isolated"):
        assert core[key]
    assert budget["verified"] and budget["N"] == 25
    assert budget["source_sha256"] == sha(ROOT / "verify_n25_own_family_budget.py")
    assert budget["necessary_boundary_internal_families"] == source["necessary_boundary_internal_families"]
    assert budget["own_two_four_six_eight_rod_caps"] == [768677, 1587443, 2546859, 4058615]


def final_gate(B, record):
    assert record["verified"] and (record["N"], record["B"]) == (25, B)
    if B == 14:
        assert record["schema"] == "independent-all-parent-N25-B14-lower-payment-chain-v1"
        assert record["source_sha256"] == sha(ROOT / "audit_n25_b14_chain.py")
        assert record["complete_necessary_parent_weak_graphs"] == TOTALS[B]
        assert record["pending_weak_graphs"] == 0 and record["complete_B14_actual_cover_lower_family_paid"]
        assert record["each_parent_id_has_exactly_one_final_status"]
        assert record["all_stage_payment_residual_partitions_compared_by_parent_identity"]
        assert record["actual_cover_origin_condition_not_a_geometric_weak_graph_exclusion"]
        assert record["fixed_completion_family_payments_not_a_geometric_weak_graph_exclusion"]
        assert record["payment_counts"] == {
            "actual-cover-origin-unexposed-center-obstruction": 160698,
            "strict-sparse-source-injection": 4893, "strict-eight-rod-integer-angle-cycle": 392,
            "fresh-standard-library-exact-weak-force": 3815,
            "fresh-branch-payment-for-prior-fixed-family": 7,
            "exact-complete-simple-hole-family": 2194,
            "refined-exact-complete-simple-hole-family": 13,
            "exact-complete-pinched-collar-filling-family": 80}
    elif B == 15:
        assert record["schema"] == "complete-origin-parent-fresh-batch-and-direct-finer-merge-v1"
        assert record["source_sha256"] == sha(ROOT / "audit_complete_origin_finer_with_direct.py")
        assert record["complete_parent_weak_graphs"] == TOTALS[B]
        assert record["remaining_weak_graphs"] == 0 and record["all_residual_weak_lower_bounds_paid"]
        assert record["all_parent_indices_disjointly_partitioned_once"]
        assert record["every_old_and_new_positive_tree_freshly_mathematically_replayed"]
        assert record["complete_outer_source_faces_exactly_equal_every_parent_graph"]
        assert record["counts"] == {
            "old-strict-weak-force": 116119, "old-strict-complete-filling-family": 23181,
            "new-strict-finer-complete-filling-family": 15}
    elif B == 16:
        assert record["schema"] == "N25-whole-parent-strict-and-same-root-family-payment-v1"
        assert record["source_sha256"] == sha(ROOT / "audit_n25_parent_mixed_supplements.py")
        assert record["complete_parent_weak_graphs"] == TOTALS[B] and record["remaining_weak_graphs"] == 0
        assert record["complete_necessary_family_lower_payments_closed"]
        assert record["all_complete_parent_source_indices_disjointly_partitioned_once"]
        assert record["nonstrict_theorem_requires_literal_whole_source_face_equality_and_actual91_type_transport"]
        assert record["attaining_parent_not_recast_as_a_strict_upper_radius_exclusion"]
        assert record["counts"] == {
            "unchanged-accepted-parent-payment": 120548,
            "new-strict-complete-family": 233, "new-nonstrict-same-root-complete-family": 1}
    else:
        assert B == 17
        assert record["schema"] == "N25-whole-source-direct-family-strict-increment-v1"
        assert record["source_sha256"] == sha(ROOT / "audit_n25_parent_direct_supplements.py")
        assert record["complete_parent_weak_graphs"] == TOTALS[B] and record["remaining_weak_graphs"] == 0
        assert record["all_complete_parent_indices_partitioned_once"]
        assert record["every_new_whole_filling_tree_freshly_mathematically_replayed"]
        assert record["all_new_conditional_proofs_require_exact_whole_parent_source_faces"]
        assert record["only_actual_accepted_parent_pending_indices_paid"]
        assert record["old_parent_proofs_reused_unchanged_without_claim_of_new_old_tree_replay"]
        p = record["previous_pending_weak_graphs"]
        assert type(p) is int and 39 <= p <= 66857
        assert record["additional_strict_complete_families"] == p
        assert record["counts"].get("pending", 0) == 0
        assert record["counts"]["new-strict-direct-family"] == p
        assert record["counts"]["unchanged-accepted-parent-payment"]+p == TOTALS[B]
    assert not record["global_optimality_proved"]


def verify_ledger(B, report, path, pendingpath):
    count, kinds = 0, Counter()
    with path.open(encoding="ascii") as stream:
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert row["parent_group" if B == 14 else "parent_index"] == count
            count += 1
            kinds[row["kind" if B == 14 else "status"]] += 1
            if B == 16 and row["status"] == "nonstrict-same-root-complete-family":
                assert row["parent_index"] == 115569
                assert row["strict_completion_types"] == 90 and row["same_root_core_completion_types"] == 1
                assert row["core_lower_radius"] == "1/(sqrt(6)+sqrt(3))"
                assert row["not_a_strict_upper_radius_weak_graph_exclusion"]
                assert row["transport_sha256"] == sha(ROOT / "n25-B16-p115569-nonstrict1/VERIFIED.json")
    assert count == TOTALS[B]
    if B == 14:
        assert dict(kinds) == report["payment_counts"]
        with pendingpath.open(encoding="ascii") as stream:
            header = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
            assert header["schema"] == "independent-all-parent-B14-chain-residual-v1"
            assert (header["N"], header["B"]) == (25, 14) and not stream.read().strip()
    else:
        assert pendingpath.stat().st_size == 0
        expected = {
            15: {"strict-exact-weak-graph-exclusion": 116119, "strict-complete-filling-family": 23196},
            16: {"strict-exact-weak-graph-exclusion": 83158,
                 "strict-complete-filling-family-exact-transport": 8068,
                 "strict-complete-filling-family": 29555, "nonstrict-same-root-complete-family": 1},
            17: {"strict-exact-weak-graph-exclusion": 223283, "strict-complete-filling-family": 66857}}
        assert dict(kinds) == expected[B]
    return dict(kinds)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    source, core, budget = map(read, (SOURCEPATH, COREPATH, BUDGETPATH))
    interface_gate(source, core, budget)
    finals = {B: read(path) for B, path in FINALPATHS.items()}
    for B, record in finals.items():
        final_gate(B, record)
    pipeline17 = read(ROOT / "n25-B17-final1/PIPELINE-COMPLETED.json")
    assert pipeline17["actual_original_and_independent_final_adopter_terminals_observed"]
    assert pipeline17["whole_necessary_B17_family_lower_paid"] and pipeline17["remaining_weak_graphs"] == 0
    assert pipeline17["final_parent_report_sha256"] == sha(FINALPATHS[17])
    assert pipeline17["source_sha256"] == sha(ROOT / "run_n25_B17_final_after_original.py")
    original17 = read(ROOT / "n25-B17-final1/ORIGINAL-B17-TERMINAL.json")
    assert original17["OriginalCachedProcessHandleTerminalObserved"] and original17["ActualExitCode"] == 0
    adopter17 = read(ROOT / "n25-B17-final1/FINAL-PARENT-AUDIT-TERMINAL.json")
    assert adopter17["actual_child_terminal_observed"] and adopter17["actual_exit_code"] == 0
    originalaudit = read(ROOT / "n25-B17-f1/FULL-PARENT-AUDIT-TERMINAL.json")
    assert originalaudit["real_process_terminal_observed"] and originalaudit["actual_exit_code"] == 0
    assert originalaudit["source_sha256"] == sha(ROOT / "audit_complete_origin_fillings.py")
    pending, bindings, inspected = deque(), {}, set()

    def add(path, expected=None):
        path = Path(path).resolve()
        assert path.is_absolute() and (
            path.is_relative_to(INCOMING) or path.is_relative_to(INCOMING.parent / "dependencies"))
        assert path.is_file(), ("missing required complete N25 proof premise", path)
        if expected is None:
            expected = sha(path)
        assert type(expected) is str and len(expected) == 64
        if path in bindings:
            assert bindings[path] == expected, ("conflicting exact content identities", path)
            return
        bindings[path] = expected
        # Read every bound JSON object, not only conventional report names:
        # historical snapshots and libraries also contain binding dictionaries.
        if path.suffix.lower() == ".json":
            pending.append(path)

    families = []
    for B, record in finals.items():
        reportpath = FINALPATHS[B]
        add(reportpath)
        ledgerdir = reportpath.parent
        ledger = ledgerdir / ("ALL-PARENT-PAYMENTS.jsonl" if B == 14 else "PAYMENTS.jsonl")
        residual = ledgerdir / ("RESIDUAL.jsonl" if B == 14 else "PENDING.jsonl")
        add(ledger, record["all_parent_ledger_sha256" if B == 14 else "payments_sha256"])
        add(residual, record["residual_sha256" if B == 14 else "pending_sha256"])
        kinds = verify_ledger(B, record, ledger, residual)
        families.append({
            "B": B, "complete_necessary_parents": TOTALS[B], "pending": 0,
            "actual_payment_kinds": kinds, "final_path": str(reportpath), "final_sha256": sha(reportpath),
            "payment_ledger_path": str(ledger), "payment_ledger_sha256": sha(ledger),
            "pending_ledger_path": str(residual), "pending_ledger_sha256": sha(residual)})
        print("N25 actual full final ledger independently scanned:", B, TOTALS[B], "parents, unpaid zero", flush=True)
    for path in (
        Path(__file__), SOURCEPATH, COREPATH, BUDGETPATH, DOCUMENT,
        ROOT / "N25-ACTUAL-FOUR-SOURCE-OBLIGATIONS-v1.md",
        ROOT / "NECESSARY-OUTER-COLLAR-ARBITRARY-COVER-INDUCTION-v1.md",
        ROOT / "N23-N24-COVER-AND-FULL-PEEL-INDUCTION-v1.md",
        HIGH / "evidence/N25-ENDPOINT-CORE-LOWER-SNAPSHOT-resume1.json",
        ROOT / "n25-B16-single-candidate-collar-closure-20261005-v1.json",
        ROOT / "n25-B16-p115569-nonstrict1/VERIFIED.json",
        ROOT / "n25-B16-final1/PIPELINE-COMPLETED.json",
        ROOT / "n25-B16-final1/EXISTING-TERMINALS.json",
        ROOT / "n25-B17-final1/PIPELINE-COMPLETED.json",
        ROOT / "n25-B17-final1/ORIGINAL-B17-TERMINAL.json",
        ROOT / "n25-B17-final1/FINAL-PARENT-AUDIT-TERMINAL.json",
        ROOT / "n25-B17-final1/FORMAL-SUPPLEMENTS.json",
        ROOT / "n25-B17-f1/COMPLETE-PAYMENT-AUDIT/VERIFIED.json",
        ROOT / "n25-B17-f1/FULL-PARENT-AUDIT-TERMINAL.json"):
        add(path)
    while pending:
        path = pending.popleft()
        if path in inspected:
            continue
        inspected.add(path)
        record = read(path)
        if not isinstance(record, dict):
            continue
        for field in ("frozen_files", "files_relative_to_workspace", "files",
                      "frozen_actual_worker_reports_and_original_families",
                      "new_global_entry_frozen_files"):
            entries = record.get(field)
            if not isinstance(entries, dict):
                continue
            # "files" is also used by some mechanical-derivation lists/maps.
            if field == "files" and not all(isinstance(value, str) and len(value) == 64
                                            for value in entries.values()):
                continue
            for name, digest in entries.items():
                target = Path(name)
                if field == "files_relative_to_workspace" or not target.is_absolute():
                    target = WORK / name
                add(target, digest)
        for name, archive in record.get("archive_bindings", {}).items():
            if isinstance(archive, dict) and "archive_sha256" in archive:
                target = Path(name)
                if not target.is_absolute():
                    assert target.name == name
                    target = INCOMING / name
                add(target, archive["archive_sha256"])
    output.mkdir()
    print("N25 whole four-family source/lower/upper/core content closure collected:", len(bindings),
          "actual files or whole archives; accepted old mathematics reused honestly", flush=True)
    mismatches = []
    with (output / "CURRENT-INPUTS.jsonl").open("x", encoding="ascii") as ledger:
        for number, path in enumerate(sorted(bindings, key=str), 1):
            if sha(path) != bindings[path]:
                mismatches.append(str(path))
            ledger.write(json.dumps({"path": str(path), "sha256": bindings[path]},
                                    separators=(",", ":"))+"\n")
            if number % 5000 == 0:
                print("N25 complete source-proof premise bytes", number, "/", len(bindings),
                      "differences", len(mismatches), flush=True)
    assert not mismatches, mismatches
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N25-four-whole-source-family-same-radical-root-current-premise-byte-closure-v1",
        "N": 25, "all_required_families": [14, 15, 16, 17],
        "complete_necessary_residual_weak_graphs": 721329,
        "all_four_actual_full_payment_ledgers_independently_sequentially_scanned": True,
        "all_parent_final_lower_chains_zero": True, "family_partitions": families,
        "actual_B17_original_and_final_adopter_successful_terminals_checked": True,
        "all_actual_nonzero_strict_library_pruning_bound_to_own_complete_source_interface": True,
        "own_exact_radical_upper_fresh_local_and_real_complete_nonstrict_core_bound": True,
        "current_files_and_whole_archives_checked": len(bindings),
        "all_current_content_bindings_checked": True, "mismatches": mismatches,
        "all_bound_JSON_objects_inspected_for_nested_snapshot_library_and_input_bindings": len(inspected),
        "current_input_ledger_sha256": sha(output / "CURRENT-INPUTS.jsonl"),
        "four_actual_source_interface_sha256": sha(SOURCEPATH),
        "same_root_upper_local_real_full_core_interface_sha256": sha(COREPATH),
        "own_family_budget_sha256": sha(BUDGETPATH), "global_source_manuscript_sha256": sha(DOCUMENT),
        "old_mathematics_honestly_reused_not_new_all_old_tree_replays": True,
        "written_math_not_claimed_machine_proved_by_content_checks": True,
        "source_sha256": sha(Path(__file__)),
        "independent_whole_current_content_audit_and_final_global_adoption_still_required": True,
        "global_optimality_proved": False})


if __name__ == "__main__":
    main()
