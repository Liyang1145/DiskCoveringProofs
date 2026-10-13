"""Bind an exact partial energy overlay into the entire actual current chain."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
import audit_stage_catalogue_with_closed_pool as history
import verify_partial_prefix_energy_overlay as overlay
import verify_conditional_force_stage as stage


def main():
    parser = argparse.ArgumentParser()
    for name in ("parent-audit", "parent-digest-recheck", "overlay", "overlay-replay", "narrative", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    parent = stage.read(args.parent_audit)
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["prior_completed_full_chain_semantic_replay_still_bound"]
            or parent["radius_scope"] != stage.SCOPE or parent["global_optimality_proved"] is not False):
        raise ValueError("partial current extension lacks the actual complete parent chain")
    parent_rehash = stage.read(args.parent_digest_recheck)
    if (not parent_rehash["all_current_file_digests_rehashed"]
            or parent_rehash["current_audit_sha256"] != stage.sha(args.parent_audit)
            or parent_rehash["current_file_digests_rechecked"] != len(parent["files"])):
        raise ValueError("partial current extension lacks the actual independent parent digest recheck")
    inventory = dict(parent["files"])
    print("Rehashing all current parent evidence and reconstructing partial source semantics.", flush=True)
    for text, digest in inventory.items():
        if stage.sha(text) != digest:
            raise ValueError("current parent bytes changed: " + text)
    accepted, paths = stage.bound(args.overlay)
    if (stage.read(args.overlay_replay) != accepted
            or accepted["parent_current_audit_sha256"] != stage.sha(args.parent_audit)
            or stage.sha(overlay.__file__) != accepted["files"]["verify_partial_prefix_energy_overlay.py"]):
        raise ValueError("partial current overlay lacks its actual matching executed frozen replay")
    values = overlay.input_gate(args.overlay)
    if values[1] != parent:
        raise ValueError("partial source changed its actual current parent audit")
    paths.extend(values[-1])
    frontier, ledger, domains, controls = overlay.derive(args.overlay, values)
    if (frontier != stage.read(args.overlay / "FRONTIER.json")
            or ledger != stage.read(args.overlay / "LOWER-LEDGER.json")
            or domains != stage.read(args.overlay / "DOMAINS.json")
            or controls != stage.read(args.overlay / "POSITIVE-CONTROLS.json")
            or len(frontier["pending_states"]) != accepted["conditional_frontier_pending_subtrees"]
            or len(ledger) != accepted["new_strict_radius_conditional_whole_partial_subtrees_excluded"]
            or F(accepted["radius_upper"]) != F(parent["r_strict_interval"][1])):
        raise ValueError("actual whole-prefix payments, domains or current frontier did not reconstruct")
    old = values[3]["pending_states"]
    selected = set(values[0]["selected_source_indices"])
    if ([row for index, row in enumerate(old) if index not in selected] != frontier["pending_states"]
            or len(old) != parent["Rstar_conditional_frontier_pending_subtrees"]
            or len(old) - len(frontier["pending_states"]) != len(ledger)):
        raise ValueError("partial overlay lost an unattempted sibling or removed the wrong prefix")
    terminals = [row for row in frontier["pending_states"] if row["terminal"]]
    if ([row for row in old if row["terminal"]] != terminals
            or len(terminals) != parent["all_current_unresolved_terminal_paths_reconstructed"]):
        raise ValueError("partial overlay changed complete terminal or candidate ownership")
    conservation = []
    for b in (14, 15, 16, 17):
        before = sum(row["B"] == b for row in old)
        removed = sum(row["B"] == b for row in ledger)
        after = sum(row["B"] == b for row in frontier["pending_states"])
        if before - removed != after:
            raise ValueError("partial whole-prefix conservation failed for a boundary family")
        conservation.append({"B": b, "source_subtrees": before,
                             "strict_partial_energy_whole_subtrees_excluded": removed,
                             "current_subtrees": after,
                             "retained_complete_terminals": sum(row["B"] == b for row in terminals)})
    old_pool = args.parent_audit.with_name(args.parent_audit.stem + "-closed-type-pool.json")
    if inventory.get(linux(old_pool)) != stage.sha(old_pool):
        raise ValueError("partial current extension lost its bound historical pool")
    pool = stage.read(old_pool)
    receipts = history.retained_pool_gate(pool, parent, F(accepted["radius_upper"]))
    pool_target = args.output.with_name(args.output.stem + "-closed-type-pool.json")
    receipt_target = args.output.with_name(args.output.stem + "-closed-receipt-checks.json")
    obligation_target = args.output.with_name(args.output.stem + "-terminal-obligations.json")
    if any(path.exists() for path in (pool_target, receipt_target, obligation_target)):
        raise FileExistsError("fresh partial current sidecars required")
    pool_target.write_bytes(old_pool.read_bytes())
    receipt_target.write_text(json.dumps(receipts, indent=2) + "\n", encoding="utf-8")
    old_obligations = stage.read(args.parent_audit.with_name(args.parent_audit.stem + "-terminal-obligations.json"))
    obligation_target.write_text(json.dumps(old_obligations, indent=2) + "\n", encoding="utf-8")
    regression = stage.read(args.overlay / "ADAPTER-REGRESSION.json")
    test_path = Path(__file__).with_name("test_partial_prefix_quadratic_kernel.py")
    if stage.sha(test_path) != regression["executed_test_sha256"]:
        raise ValueError("partial adapter regression runner changed")
    paths.extend([args.parent_audit, args.parent_digest_recheck, args.overlay_replay, args.narrative, pool_target, receipt_target,
                  obligation_target, Path(__file__), Path(overlay.__file__), Path(history.__file__), test_path,
                  Path(__file__).with_name("recheck_partial_energy_current_inventory.py"),
                  Path(__file__).with_name("n26-partial-prefix-energy-proof.md"),
                  Path(__file__).with_name("n26_partial_prefix_quadratic_kernel.py"),
                  Path(__file__).with_name("probe_partial_prefix_energy.py"),
                  Path(__file__).with_name("n26-partial-prefix-energy-discovery-v1.json"),
                  Path(__file__).with_name("n26-partial-prefix-energy-kernels-v1.json")])
    for path in paths:
        text, digest = linux(path), stage.sha(path)
        if text in inventory and inventory[text] != digest:
            raise ValueError("old and new partial current dependencies disagree")
        inventory[text] = digest
    print("Rehashing the final current chain including every historical proof receipt.", flush=True)
    for text, digest in inventory.items():
        if stage.sha(text) != digest:
            raise ValueError("partial current bytes changed during final binding")
    report = {key: value for key, value in parent.items() if key != "files"}
    report.update({
        "schema": "N26-complete-current-chain-with-exact-partial-prefix-energy-audit-v1",
        "prior_current_audit_sha256": stage.sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "current_bound_bytes_rechecked": True,
        "current_partial_energy_actual_published_replay_matched_and_semantics_replayed_here": True,
        "source_conditional_pending_subtrees_before_partial_energy": len(old),
        "source_conditional_pending_subtrees": len(old),
        "new_strict_radius_conditional_partial_energy_whole_subtrees_excluded": len(ledger),
        "latest_enumeration_strict_whole_subtrees_excluded": parent[
            "new_strict_radius_conditional_whole_subtrees_excluded"],
        "new_strict_radius_conditional_whole_subtrees_excluded": len(ledger),
        "Rstar_conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "Rstar_conditional_frontier_families": frontier["families"],
        "previous_enumeration_frontier_conservation_per_family": parent[
            "frontier_conservation_per_family_independently_checked"],
        "frontier_conservation_per_family_independently_checked": conservation,
        "current_frontier_actual_acceptance": linux(args.overlay / "VERIFIED.json"),
        "current_frontier_actual_file": linux(args.overlay / "FRONTIER.json"),
        "all_current_native_partial_prefixes_inverse_identities_and_full_roots_rechecked": len(ledger),
        "current_partial_energy_minimum_strict_radius_margin": accepted["minimum_strict_radius_margin"],
        "all_unattempted_raw_subtrees_and_all_complete_terminals_retained_identically": True,
        "all_current_unresolved_terminal_paths_reconstructed": len(terminals),
        "all_current_terminal_obligations_unchanged_by_nonterminal_partial_overlay": True,
        "joined_closed_full_type_codes_in_these_two_catalogues": len(pool),
        "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked": len(receipts),
        "partial_energy_adapter_regression_controls": regression["regression_controls_passed"],
        "partial_energy_overlay_negative_controls_rejected": accepted["negative_controls_rejected"],
        "original_U_frontier_nodes_removed_by_partial_energy_overlay": 0,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": inventory})
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
