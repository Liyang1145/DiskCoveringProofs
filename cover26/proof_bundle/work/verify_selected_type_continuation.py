"""Bind selected-type refinements while preserving every previously paid node."""

import argparse
import json
from pathlib import Path

from audit_prefix_partition import linux
from verify_selected_type_trees import SCOPE, bound, read
from verify_terminal_catalog import local_path, sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--old", type=Path, required=True)
    parser.add_argument("--new", type=Path, required=True)
    parser.add_argument("--old-replay", type=Path, required=True)
    parser.add_argument("--new-replay", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    old_report, inventory = bound(args.old)
    new_report, files = bound(args.new)
    inventory.extend(files)
    inventory.extend([args.old_replay, args.new_replay, Path(__file__)])
    if (read(args.old_replay) != old_report or read(args.new_replay) != new_report
            or old_report["radius_scope"] != SCOPE or new_report["radius_scope"] != SCOPE
            or old_report["source_acceptance_sha256"] != new_report["source_acceptance_sha256"]
            or old_report["radius_upper"] != new_report["radius_upper"]):
        raise ValueError("selected-type continuation changed an accepted source, replay or scope")
    old, new = read(args.old / "CERTIFICATE.json"), read(args.new / "CERTIFICATE.json")
    if ({key: value for key, value in old.items() if key != "types"}
            != {key: value for key, value in new.items() if key != "types"}
            or [row["group_index"] for row in old["types"]] != [row["group_index"] for row in new["types"]]):
        raise ValueError("selected-type continuation skipped or reordered a canonical type")
    preserved, opened, added, refined = 0, 0, 0, []
    for previous, current in zip(old["types"], new["types"]):
        if previous["spec"] != current["spec"]:
            raise ValueError("selected-type continuation changed the canonical face complex")
        if previous.get("sharp_domain_empty"):
            if previous != current:
                raise ValueError("a previously closed necessary root was overwritten")
            continue
        old_nodes, new_nodes = previous["nodes"], current["nodes"]
        if len(new_nodes) < len(old_nodes):
            raise ValueError("selected-type continuation shortened a previous tree")
        refinements = 0
        for index, node in enumerate(old_nodes):
            if node["kind"] != "OPEN":
                if new_nodes[index] != node:
                    raise ValueError("a previously paid leaf or complete closed split changed")
                preserved += 1
            elif new_nodes[index] == node:
                opened += 1
            else:
                if new_nodes[index]["kind"] not in ("SPLIT", "DIRECT_FORCE", "CORRELATED_FORCE", "EMPTY"):
                    raise ValueError("old OPEN changed to an invalid refinement")
                refinements += 1
        added += len(new_nodes) - len(old_nodes)
        refined.append({"group_index": previous["group_index"],
                        "old_nodes": len(old_nodes), "new_nodes": len(new_nodes),
                        "old_OPEN_roots_refined": refinements})
    old_excluded = set(old_report["strict_radius_conditional_type_exclusions"])
    new_excluded = set(new_report["strict_radius_conditional_type_exclusions"])
    if not old_excluded <= new_excluded:
        raise ValueError("previous complete radius-conditional exclusions were lost")
    digests = {linux(path): sha(path) for path in inventory}
    report = {"schema": "N26-selected-type-paid-node-preserving-continuation-v1", "verified": True,
              "radius_scope": SCOPE, "old_acceptance_sha256": sha(args.old / "VERIFIED.json"),
              "new_acceptance_sha256": sha(args.new / "VERIFIED.json"),
              "all_prior_non_OPEN_nodes_and_closed_splits_unchanged": True,
              "previous_non_OPEN_nodes_preserved": preserved,
              "previous_OPEN_nodes_still_OPEN": opened, "additional_tree_nodes": added,
              "new_closed_competitor_type_indices": sorted(new_excluded - old_excluded),
              "per_type": refined,
              "both_exact_standalone_acceptances_replayed_and_matched": True,
              "all_original_U_frontiers_unchanged": True,
              "full_catalog_complete": False, "global_optimality_proved": False,
              "files": digests}
    for text, digest in digests.items():
        if sha(local_path(text)) != digest:
            raise ValueError("selected-type continuation inputs changed during binding")
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
