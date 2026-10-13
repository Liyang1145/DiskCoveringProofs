"""Preserve full proof trees across two catalogues by complete canonical spec."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import local_path, sha


def code(row):
    return row["spec"]["B"], tuple(row["spec"]["faces"])


def nodes(row, pool):
    if row["kind"] == "REUSE":
        original = pool[row["pool_type_index"]]
        if original["spec"] != row["spec"]:
            raise ValueError("catalogue transfer reused a different full proof")
        return original
    return row


def lineage(old, new):
    if old["spec"] != new["spec"]:
        raise ValueError("catalogue transfer changed a full canonical face complex")
    if old.get("sharp_domain_empty"):
        if not new.get("sharp_domain_empty"):
            raise ValueError("catalogue transfer reopened a closed empty root")
        return 0, 0
    old_nodes, new_nodes = old["nodes"], new["nodes"]
    if len(new_nodes) < len(old_nodes):
        raise ValueError("catalogue transfer lost old proof tree nodes")
    preserved = 0
    for index, node in enumerate(old_nodes):
        if node["kind"] != "OPEN":
            if new_nodes[index] != node:
                raise ValueError("catalogue transfer changed an old paid node or closed split")
            preserved += 1
        elif new_nodes[index] != node and new_nodes[index]["kind"] not in (
                "DIRECT_FORCE", "CORRELATED_FORCE", "EMPTY", "SPLIT"):
            raise ValueError("catalogue transfer replaced OPEN by an invalid node")
    return preserved, len(new_nodes) - len(old_nodes)


def transfer(old_folder, new_folder):
    old_manifest, new_manifest = read(old_folder / "MANIFEST.json"), read(new_folder / "MANIFEST.json")
    old, new = read(old_folder / "CERTIFICATE.json"), read(new_folder / "CERTIFICATE.json")
    if any(old[key] != new[key] for key in ("radius_scope", "radius_upper", "pool_acceptance_sha256")):
        raise ValueError("catalogue proof transfer changed root, domain protocol or proof pool")
    old_pool_folder, new_pool_folder = local_path(old_manifest["source_pool"]), local_path(new_manifest["source_pool"])
    old_pool = {row["group_index"]: row for row in read(old_pool_folder / "CERTIFICATE.json")["types"]}
    new_pool = {row["group_index"]: row for row in read(new_pool_folder / "CERTIFICATE.json")["types"]}
    old_types, new_types = {code(row): row for row in old["types"]}, {code(row): row for row in new["types"]}
    if len(old_types) != len(old["types"]) or len(new_types) != len(new["types"]):
        raise ValueError("catalogue has repeated full canonical competitor codes")
    old_rows = {code(row): row for row in read(old_folder / "CLASSIFICATION.json")}
    new_rows = {code(row): row for row in read(new_folder / "CLASSIFICATION.json")}
    old_domains = {row["group_index"]: row["matrix"] for row in read(old_folder / "DOMAINS.json")}
    new_domains = {row["group_index"]: row["matrix"] for row in read(new_folder / "DOMAINS.json")}
    matched, absent, fresh, preserved, added = [], [], [], 0, 0
    for key, previous in old_types.items():
        current = new_types.get(key)
        if current is None:
            if not old_rows[key]["radius_at_most_Rstar_type_excluded"]:
                raise ValueError("an old still-unclosed full type disappeared from the new current catalogue")
            absent.append({"old_group_index": previous["group_index"], "spec": previous["spec"],
                           "old_complete_proof_kept_bound_not_claimed_rerun": True})
            continue
        if old_domains[previous["group_index"]] != new_domains[current["group_index"]]:
            raise ValueError("catalogue transfer changed an identical type's necessary matrix")
        p, a = lineage(nodes(previous, old_pool), nodes(current, new_pool))
        preserved += p
        added += a
        if (old_rows[key]["radius_at_most_Rstar_type_excluded"]
                and not new_rows[key]["radius_at_most_Rstar_type_excluded"]):
            raise ValueError("catalogue transfer lost a complete type exclusion")
        matched.append({"old_group_index": previous["group_index"],
                        "new_group_index": current["group_index"], "spec": previous["spec"],
                        "old_non_OPEN_nodes_preserved": p, "added_nodes": a,
                        "identical_full_root_spec_radius_and_matrix": True,
                        "previous_complete_type_exclusion_preserved": old_rows[key]["radius_at_most_Rstar_type_excluded"]})
    for key, row in new_types.items():
        if key not in old_types:
            fresh.append({"new_group_index": row["group_index"], "spec": row["spec"],
                          "new_full_domain_tree_explicitly_present": True})
    old_paid = read(old_folder / "CONDITIONAL-REMOVAL-LEDGER.json")
    new_frontier = read(new_folder / "RSTAR-COMPETITOR-FRONTIER.json")
    for state in new_frontier["pending_states"]:
        for old_payment in old_paid:
            if (state["B"] == old_payment["B"]
                    and old_payment["prefix"][:len(state["prefix"])] == state["prefix"]):
                raise ValueError("new frontier reopened an old excluded full terminal or its ancestor")
    old_table, new_table = read(old_folder / "SOURCE-CATALOG.json"), read(new_folder / "SOURCE-CATALOG.json")
    candidate_codes = []
    for table in (old_table, new_table):
        candidates = [row for row in table["groups"] if any(
            table["rows"][member]["same_canonical_type_as_known_candidate"] for member in row["member_indices"])]
        if len(candidates) != 1:
            raise ValueError("candidate has ambiguous full canonical type ownership")
        candidate_codes.append((candidates[0]["B"], tuple(candidates[0]["canonical_faces"])))
    if candidate_codes[0] != candidate_codes[1]:
        raise ValueError("candidate canonical graph changed across catalogue transfer")
    return {"matched_full_types": matched, "absent_old_closed_type_proofs_still_bound": absent,
            "fresh_new_full_type_roots": fresh, "previous_non_OPEN_nodes_preserved": preserved,
            "additional_transferred_tree_nodes": added}


def main():
    parser = argparse.ArgumentParser()
    for key in ("old", "new", "old-replay", "new-replay", "report"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    old, inventory = bound(args.old)
    new, paths = bound(args.new)
    inventory.extend(paths)
    if (read(args.old_replay) != old or read(args.new_replay) != new
            or old["radius_scope"] != new["radius_scope"] or old["radius_upper"] != new["radius_upper"]
            or old["r_strict_interval"] != new["r_strict_interval"]):
        raise ValueError("full catalogue transfer lacks actual matching same-root standalone replays")
    result = transfer(args.old, args.new)
    first = result["matched_full_types"][0]
    bad = deepcopy(read(args.new / "CERTIFICATE.json"))
    changed = next(row for row in bad["types"] if row["group_index"] == first["new_group_index"])
    if changed["kind"] == "TREE":
        old_certificate = read(args.old / "CERTIFICATE.json")
        original = next(row for row in old_certificate["types"] if row["group_index"] == first["old_group_index"])
        node = next(item for item in changed["nodes"] if item["kind"] != "OPEN")
        node.clear()
        node["kind"] = "OPEN"
        try:
            lineage(original, changed)
        except ValueError:
            rejected = ["old-paid-node-erased-during-canonical-code-transfer"]
        else:
            raise AssertionError("full catalogue transfer accepted an erased old paid node")
    else:
        rejected = []
    inventory.extend([args.old_replay, args.new_replay, Path(__file__)])
    hashes = {linux(path): sha(path) for path in inventory}
    for text, digest in hashes.items():
        if sha(local_path(text)) != digest:
            raise ValueError("catalogue transfer dependency changed")
    report = {
        "schema": "N26-accepted-full-canonical-type-catalogue-proof-transfer-v1",
        "verified": True, "radius_scope": old["radius_scope"],
        "old_acceptance_sha256": sha(args.old / "VERIFIED.json"),
        "new_acceptance_sha256": sha(args.new / "VERIFIED.json"),
        "actual_old_and_new_published_replays_matched_and_bound": True,
        "all_old_paid_nodes_and_closed_splits_preserved_by_full_spec": True,
        "all_old_unclosed_types_present_in_new_current_catalogue": True,
        "no_old_removed_full_terminal_or_ancestor_reopened": True,
        "candidate_full_canonical_graph_unchanged": True,
        **result, "negative_controls_rejected": rejected,
        "global_optimality_proved": False, "files": hashes}
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("files", "matched_full_types", "absent_old_closed_type_proofs_still_bound",
                                     "fresh_new_full_type_roots")},
                     indent=2), flush=True)
    print(json.dumps({"matched": len(result["matched_full_types"]),
                      "old_closed_proofs_kept_for_absent_types": len(result["absent_old_closed_type_proofs_still_bound"]),
                      "fresh_full_types": len(result["fresh_new_full_type_roots"])}), flush=True)


if __name__ == "__main__":
    main()
