"""Preserve every old full-type paid node and closed split across registries."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import local_path, sha


def lineage(old, new):
    if ({key: value for key, value in old.items() if key != "types"}
            != {key: value for key, value in new.items() if key != "types"}
            or [row["group_index"] for row in old["types"]]
            != [row["group_index"] for row in new["types"]]):
        raise ValueError("registry continuation changed graph scope, source root or type ownership")
    preserved, retained, refined, added = 0, 0, 0, 0
    for previous, current in zip(old["types"], new["types"]):
        if previous["spec"] != current["spec"] or previous["kind"] != current["kind"]:
            raise ValueError("registry continuation changed a full spec or proof source protocol")
        if previous["kind"] == "REUSE" or previous.get("sharp_domain_empty"):
            if previous != current:
                raise ValueError("registry continuation overwrote a reused or closed empty domain")
            continue
        old_nodes, new_nodes = previous["nodes"], current["nodes"]
        if len(new_nodes) < len(old_nodes):
            raise ValueError("registry continuation lost old tree nodes")
        added += len(new_nodes) - len(old_nodes)
        for index, node in enumerate(old_nodes):
            if node["kind"] != "OPEN":
                if new_nodes[index] != node:
                    raise ValueError("registry continuation changed an old paid leaf or closed split")
                preserved += 1
            elif new_nodes[index] == node:
                retained += 1
            else:
                candidate = new_nodes[index]
                if candidate["kind"] not in ("EMPTY", "DIRECT_FORCE", "CORRELATED_FORCE", "SPLIT"):
                    raise ValueError("registry continuation replaced OPEN by an invalid proof kind")
                if candidate["kind"] == "SPLIT" and any(child < len(old_nodes) for child in candidate["children"]):
                    raise ValueError("registry continuation reused an old node as a new split child")
                refined += 1
    return {"old_TREE_non_OPEN_nodes_preserved": preserved, "old_TREE_OPEN_nodes_still_OPEN": retained,
            "old_TREE_OPEN_roots_refined": refined, "additional_TREE_nodes": added}


def main():
    parser = argparse.ArgumentParser()
    for key in ("old", "new", "old-replay", "new-replay", "report"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    old_report, inventory = bound(args.old)
    new_report, files = bound(args.new)
    inventory.extend(files)
    if (read(args.old_replay) != old_report or read(args.new_replay) != new_report
            or old_report["radius_scope"] != new_report["radius_scope"]
            or old_report["radius_upper"] != new_report["radius_upper"]
            or old_report["catalog_acceptance_sha256"] != new_report["catalog_acceptance_sha256"]
            or old_report["pool_acceptance_sha256"] != new_report["pool_acceptance_sha256"]):
        raise ValueError("registry continuation lacks actual matched replays of the same full domain")
    old, new = read(args.old / "CERTIFICATE.json"), read(args.new / "CERTIFICATE.json")
    preservation = lineage(old, new)
    old_frontier = read(args.old / "RSTAR-COMPETITOR-FRONTIER.json")
    new_frontier = read(args.new / "RSTAR-COMPETITOR-FRONTIER.json")
    old_removal = read(args.old / "CONDITIONAL-REMOVAL-LEDGER.json")
    new_removal = read(args.new / "CONDITIONAL-REMOVAL-LEDGER.json")
    key = lambda row: (row["B"], tuple(row["prefix"]))
    old_keys = {key(row): row for row in old_frontier["pending_states"]}
    new_keys = {key(row): row for row in new_frontier["pending_states"]}
    old_paid = {key(row): row for row in old_removal}
    new_paid = {key(row): row for row in new_removal}
    if (not set(new_keys) <= set(old_keys) or not set(old_paid) <= set(new_paid)
            or set(old_keys) - set(new_keys) != set(new_paid) - set(old_paid)
            or any(new_keys[k] != old_keys[k] for k in new_keys)
            or any(new_paid[k] != old_paid[k] for k in old_paid)):
        raise ValueError("registry refinement lost a sibling, changed an old payment or revived a paid terminal")
    if not set(old_report["strict_radius_conditional_current_type_exclusions"]) <= set(
            new_report["strict_radius_conditional_current_type_exclusions"]):
        raise ValueError("registry continuation lost a whole-type exclusion")
    bad = deepcopy(new)
    victim = next(row for row in bad["types"] if row["kind"] == "TREE" and "nodes" in row)
    node = next(item for item in victim["nodes"] if item["kind"] != "OPEN")
    node.clear()
    node["kind"] = "OPEN"
    try:
        lineage(old, bad)
    except ValueError:
        rejected = ["old-paid-node-or-closed-split-erased"]
    else:
        raise AssertionError("registry lineage accepted a changed old paid node")
    inventory.extend([args.old_replay, args.new_replay, Path(__file__)])
    hashes = {linux(path): sha(path) for path in inventory}
    for text, digest in hashes.items():
        if sha(local_path(text)) != digest:
            raise ValueError("registry continuation proof bytes changed")
    report = {
        "schema": "N26-accepted-expanded-registry-paid-node-preserving-continuation-v1",
        "verified": True, "radius_scope": old_report["radius_scope"],
        "old_acceptance_sha256": sha(args.old / "VERIFIED.json"),
        "new_acceptance_sha256": sha(args.new / "VERIFIED.json"),
        "both_actual_sealed_standalone_replays_matched_and_bound": True,
        "all_prior_TREE_paid_nodes_and_closed_splits_unchanged": True,
        "all_identical_REUSE_full_proofs_and_OPEN_boxes_preserved": True,
        **preservation,
        "old_unresolved_competitor_closed_boxes": old_report["unresolved_current_competitor_closed_boxes"],
        "new_unresolved_competitor_closed_boxes": new_report["unresolved_current_competitor_closed_boxes"],
        "new_full_type_exclusions": sorted(set(new_report["strict_radius_conditional_current_type_exclusions"])
                                           - set(old_report["strict_radius_conditional_current_type_exclusions"])),
        "new_current_terminal_paths_removed": len(new_paid) - len(old_paid),
        "all_unremoved_current_states_preserved_byte_semantically": True,
        "negative_controls_rejected": rejected,
        "global_optimality_proved": False, "files": hashes}
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
