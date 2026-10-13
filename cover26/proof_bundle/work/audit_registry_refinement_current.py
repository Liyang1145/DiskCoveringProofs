"""Extend the current full chain with a paid-node-preserving registry refinement."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
import verify_conditional_force_stage as binding
import verify_expanded_registry_continuation as continuation


def main():
    parser = argparse.ArgumentParser()
    for key in ("parent-audit", "old-registry", "new-registry", "new-replay",
                "continuation-report", "narrative", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    parent = binding.read(args.parent_audit)
    if (not parent["current_bound_bytes_rechecked"]
            or not parent["prior_completed_full_chain_semantic_replay_still_bound"]
            or not parent["all_siblings_unclosed_types_OPEN_boxes_and_previous_proofs_retained"]
            or parent["global_optimality_proved"]):
        raise ValueError("registry refinement has no accepted current chain")
    inventory = dict(parent["files"])
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("current parent byte changed: " + text)
    old, old_files = binding.bound(args.old_registry)
    new, files = binding.bound(args.new_registry)
    preservation = binding.read(args.continuation_report)
    if (inventory.get(linux(args.old_registry / "VERIFIED.json")) != binding.sha(args.old_registry / "VERIFIED.json")
            or binding.read(args.new_replay) != new or not preservation["verified"]
            or not preservation["all_prior_TREE_paid_nodes_and_closed_splits_unchanged"]
            or not preservation["all_identical_REUSE_full_proofs_and_OPEN_boxes_preserved"]
            or preservation["old_acceptance_sha256"] != binding.sha(args.old_registry / "VERIFIED.json")
            or preservation["new_acceptance_sha256"] != binding.sha(args.new_registry / "VERIFIED.json")
            or new["r_strict_interval"] != parent["r_strict_interval"]
            or new["radius_scope"] != parent["radius_scope"]
            or old["conditional_frontier_pending_subtrees"] != parent["Rstar_conditional_frontier_pending_subtrees"]
            or old["unresolved_current_competitor_closed_boxes"] != parent["unresolved_current_competitor_closed_boxes"]):
        raise ValueError("registry refinement changed its exact parent, radius or paid-node lineage")
    fresh_preservation = continuation.lineage(binding.read(args.old_registry / "CERTIFICATE.json"),
                                              binding.read(args.new_registry / "CERTIFICATE.json"))
    if any(preservation[key] != value for key, value in fresh_preservation.items()):
        raise ValueError("registry paid-node lineage did not freshly reconstruct")
    old_frontier = binding.read(args.old_registry / "RSTAR-COMPETITOR-FRONTIER.json")
    new_frontier = binding.read(args.new_registry / "RSTAR-COMPETITOR-FRONTIER.json")
    old_paid = binding.read(args.old_registry / "CONDITIONAL-REMOVAL-LEDGER.json")
    new_paid = binding.read(args.new_registry / "CONDITIONAL-REMOVAL-LEDGER.json")
    key = lambda row: (row["B"], tuple(row["prefix"]))
    old_states = {key(row): row for row in old_frontier["pending_states"]}
    new_states = {key(row): row for row in new_frontier["pending_states"]}
    old_payments = {key(row): row for row in old_paid}
    new_payments = {key(row): row for row in new_paid}
    if (not set(new_states) <= set(old_states) or not set(old_payments) <= set(new_payments)
            or set(old_states) - set(new_states) != set(new_payments) - set(old_payments)
            or any(new_states[k] != old_states[k] for k in new_states)
            or any(new_payments[k] != old_payments[k] for k in old_payments)
            or len(new_states) != new["conditional_frontier_pending_subtrees"]):
        raise ValueError("registry refinement lost an old sibling, terminal or payment")
    for text, digest in preservation["files"].items():
        if binding.sha(text) != digest:
            raise ValueError("registry continuation proof byte changed")
        if text in inventory and inventory[text] != digest:
            raise ValueError("registry continuation and current chain disagree")
        inventory[text] = digest
    files.extend([args.parent_audit, args.new_replay, args.continuation_report,
                  Path(__file__), Path(continuation.__file__), args.narrative])
    for path in files:
        name, digest = linux(path), binding.sha(path)
        if name in inventory and inventory[name] != digest:
            raise ValueError("new and old registry binding bytes disagree")
        inventory[name] = digest
    for text, digest in inventory.items():
        if binding.sha(text) != digest:
            raise ValueError("registry current bytes changed during final binding")
    result = {key: value for key, value in parent.items() if key != "files"}
    result.update({
        "schema": "N26-current-full-chain-paid-node-preserving-registry-refinement-v1",
        "prior_current_audit_sha256": binding.sha(args.parent_audit),
        "prior_current_file_digests_rechecked": len(parent["files"]),
        "current_registry_actual_sealed_published_replay_matched_and_bound": True,
        "current_registry_paid_node_preservation_freshly_reconstructed": True,
        "current_registry_old_TREE_OPEN_roots_refined": fresh_preservation["old_TREE_OPEN_roots_refined"],
        "current_registry_additional_TREE_nodes": fresh_preservation["additional_TREE_nodes"],
        "current_registry_new_whole_type_exclusions": preservation["new_full_type_exclusions"],
        "current_registry_additional_current_terminal_paths_removed": len(new_payments) - len(old_payments),
        "strict_radius_conditional_current_type_exclusions": new["strict_radius_conditional_current_type_exclusions"],
        "new_complete_terminal_paths_removed": len(new_paid),
        "unresolved_current_competitor_types": new["unresolved_current_competitor_types"],
        "unresolved_current_competitor_closed_boxes": new["unresolved_current_competitor_closed_boxes"],
        "Rstar_conditional_frontier_pending_subtrees": new["conditional_frontier_pending_subtrees"],
        "Rstar_conditional_frontier_families": new["conditional_frontier_families"],
        "files": inventory})
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in result.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
