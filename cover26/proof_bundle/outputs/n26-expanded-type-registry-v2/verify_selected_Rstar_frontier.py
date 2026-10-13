"""An explicit conditional partition; the original U frontier is immutable."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

import verify_terminal_catalog as catalog
from verify_selected_type_trees import SCOPE, bound, coverage_gate, read


def source_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != "N26-selected-Rstar-competitor-frontier-input-bindings-v1":
        raise ValueError("wrong conditional frontier manifest")
    for name, digest in manifest["copied_files"].items():
        if catalog.sha(folder / name) != digest:
            raise ValueError("conditional frontier sealed input changed")
    types_folder = catalog.local_path(manifest["source_types"])
    accepted, inventory = bound(types_folder)
    if (catalog.sha(types_folder / "VERIFIED.json") != manifest["source_acceptance_sha256"]
            or catalog.sha(folder / "SOURCE-TYPE-ACCEPTANCE.json") != manifest["source_acceptance_sha256"]
            or accepted["radius_scope"] != SCOPE
            or accepted["original_U_frontier_nodes_removed"] != 0
            or accepted["Rstar_competitor_frontier_nodes_removed_by_this_bundle"] != 0
            or not accepted["all_six_selected_competitor_types_accounted_for"]):
        raise ValueError("type exclusions lack the accepted conditional scope")
    published = catalog.local_path(manifest["source_types_published_replay"])
    if read(published) != accepted:
        raise ValueError("selected-type standalone replay has not matched its acceptance")
    inventory.append(published)
    for original, name in (("CLASSIFICATION.json", "SOURCE-CLASSIFICATION.json"),
                           ("CERTIFICATE.json", "SOURCE-TYPE-CERTIFICATE.json"),
                           ("PENDING-TYPES.json", "SOURCE-PENDING-TYPES.json"),
                           ("CANDIDATE-POSITIVE-CONTROL.json", "CANDIDATE-POSITIVE-CONTROL.json")):
        if catalog.sha(folder / name) != accepted["files"][original]:
            raise ValueError("conditional partition substituted a type classification")
    cat_folder = catalog.local_path(read(types_folder / "MANIFEST.json")["source_folders"]["catalog"])
    values = catalog.input_gate(cat_folder)
    table = catalog.reconstruct(cat_folder, *values[1:])
    if table != read(cat_folder / "CATALOG.json") or table != read(types_folder / "CATALOG-SOURCE/CATALOG.json"):
        raise ValueError("conditional partition did not reconstruct every canonical member")
    stage_folder, source_report, source = values[1:4]
    if (catalog.sha(folder / "SOURCE-ORIGINAL-U-ACCEPTANCE.json") != catalog.sha(stage_folder / "VERIFIED.json")
            or catalog.sha(folder / "SOURCE-ORIGINAL-U-FRONTIER.json") != source_report["files"]["FRONTIER.json"]
            or read(folder / "SOURCE-ORIGINAL-U-FRONTIER.json") != source):
        raise ValueError("conditional frontier is not a copy of the unchanged original U frontier")
    inventory.extend([stage_folder / "VERIFIED.json", stage_folder / "FRONTIER.json"])
    certificate = read(folder / "SOURCE-TYPE-CERTIFICATE.json")
    candidate_group = coverage_gate(certificate["types"], table)
    classifications = read(folder / "SOURCE-CLASSIFICATION.json")
    pending = read(folder / "SOURCE-PENDING-TYPES.json")
    if ([row["group_index"] for row in classifications] != [row["group_index"] for row in certificate["types"]]
            or [row["group_index"] for row in pending] != [row["group_index"] for row in classifications]):
        raise ValueError("a partial or excluded type disappeared from the conditional partition")
    if ([row["group_index"] for row in classifications if row["radius_at_most_Rstar_type_excluded"]]
            != accepted["strict_radius_conditional_type_exclusions"]):
        raise ValueError("conditional partition overclaimed the accepted excluded types")
    return manifest, accepted, inventory, source_report, source, table, classifications, pending, values[5], candidate_group


def derive(source, table, classifications, pending, candidate):
    removals = {}
    for row, unresolved in zip(classifications, pending):
        index = row["group_index"]
        group = table["groups"][index]
        if (row["radius_scope"] != SCOPE or unresolved["group_index"] != index
                or row["spec"] != unresolved["spec"]
                or row["spec"] != {"N": 26, "B": group["B"], "next": 26, "faces": group["canonical_faces"]}
                or row["unresolved_closed_boxes"] != len(unresolved["closed_OPEN_boxes"])
                or row["radius_at_most_Rstar_type_excluded"] != (not unresolved["closed_OPEN_boxes"])):
            raise ValueError("unresolved type or angle box was silently discarded")
        members = []
        for member in group["member_indices"]:
            actual = table["rows"][member]
            if actual["same_canonical_type_as_known_candidate"]:
                raise ValueError("known feasible candidate cannot be a conditional removal")
            members.append({"catalog_member_index": member, "B": actual["B"], "prefix": actual["prefix"],
                            "canonical_bijections": actual["canonical"]["canonical_bijections"]})
        if row["members"] != members:
            raise ValueError("conditional removal does not have every checked member isomorphism")
        if not row["radius_at_most_Rstar_type_excluded"]:
            continue
        for member in members:
            key = (member["B"], tuple(member["prefix"]))
            if key in removals:
                raise ValueError("terminal member was removed twice")
            removals[key] = {"group_index": index, **member, "canonical_spec": row["spec"],
                             "radius_scope": SCOPE,
                             "minimum_strict_margin_above_same_root_upper": row["minimum_strict_margin"]}
    kept, paid, source_keys = [], [], set()
    for state in source["pending_states"]:
        key = (state["B"], tuple(state["prefix"]))
        if key in source_keys:
            raise ValueError("source U frontier has repeated ownership")
        source_keys.add(key)
        if key in removals:
            payment = removals[key]
            member = table["rows"][payment["catalog_member_index"]]
            if (state["next"] != 26 or state["faces"] != member["faces"]
                    or state["pending"] or state["faces"] != table["rows"][payment["catalog_member_index"]]["faces"]):
                raise ValueError("conditional type exclusion was applied to a partial or different subtree")
            paid.append({**payment, "unchanged_original_U_state": state})
        else:
            kept.append(state)
    if len(paid) != len(removals):
        raise ValueError("a certified terminal member is absent from its bound original frontier")
    for row in classifications:
        if not row["radius_at_most_Rstar_type_excluded"]:
            for member in row["members"]:
                if not any(state["B"] == member["B"] and state["prefix"] == member["prefix"] for state in kept):
                    raise ValueError("a still-unclosed competitor terminal vanished")
    owners = [state for state in kept if state["B"] == 16
              and candidate["prefix"][:len(state["prefix"])] == state["prefix"]]
    if len(owners) != 1 or owners[0]["prefix"] != candidate["prefix"]:
        raise ValueError("candidate lost its unique full terminal owner")
    families = [{"B": b, "I": 26 - b,
                 "pending_subtrees": sum(state["B"] == b for state in kept),
                 "pending_terminal_subtrees": sum(state["B"] == b and state["next"] == 26
                                                   and not state["pending"] for state in kept)}
                for b in (14, 15, 16, 17)]
    frontier = {"schema": "N26-radius-at-most-same-root-conditional-competitor-frontier-v1",
                "radius_scope": SCOPE, "source_original_U_pending_subtrees": len(source["pending_states"]),
                "radius_conditional_terminal_paths_removed": len(paid),
                "families": families, "pending_states": kept,
                "all_nonremoved_original_U_states_preserved_byte_semantically": True,
                "unresolved_selected_competitor_types_retained": sum(
                    not row["radius_at_most_Rstar_type_excluded"] for row in classifications),
                "known_feasible_candidate_retained": candidate["prefix"],
                "original_U_frontier_rewritten": False,
                "full_catalog_complete": False, "global_optimality_proved": False}
    if len(kept) + len(paid) != len(source["pending_states"]):
        raise ValueError("conditional partition lost a source subtree")
    return frontier, paid


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    manifest, accepted, inventory, source_report, source, table, classifications, pending, candidate, group = source_gate(args.input)
    original_digests = {str(path): catalog.sha(path) for path in inventory}
    frontier, paid = derive(source, table, classifications, pending, candidate)
    negatives = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid conditional frontier accepted: " + label)

    first = next(row for row in classifications if row["radius_at_most_Rstar_type_excluded"])
    bad = deepcopy(classifications)
    bad[first["group_index"]]["members"] = bad[first["group_index"]]["members"][:-1]
    reject("paid-type-member-isomorphism-missing", lambda: derive(source, table, bad, pending, candidate))
    bad = deepcopy(source)
    victim = first["members"][0]
    state = next(row for row in bad["pending_states"] if row["B"] == victim["B"] and row["prefix"] == victim["prefix"])
    state["next"] = 25
    reject("full-type-exclusion-applied-to-partial-subtree", lambda: derive(bad, table, classifications, pending, candidate))
    bad = deepcopy(source)
    bad["pending_states"] = [row for row in bad["pending_states"] if row["prefix"] != candidate["prefix"]]
    reject("known-candidate-terminal-dropped", lambda: derive(bad, table, classifications, pending, candidate))
    bad_pending = deepcopy(pending)
    bad_pending[first["group_index"]]["closed_OPEN_boxes"] = [{"index": 0}]
    reject("closed-type-claim-with-hidden-OPEN-box", lambda: derive(source, table, classifications, bad_pending, candidate))
    bad = deepcopy(classifications)
    bad[0]["radius_scope"] = "unconditional-original-U"
    reject("conditional-payment-promoted-to-original-U-exclusion",
           lambda: derive(source, table, bad, pending, candidate))
    for name, data in (("RSTAR-COMPETITOR-FRONTIER.json", frontier), ("CONDITIONAL-REMOVAL-LEDGER.json", paid)):
        target = args.input / name
        if target.exists():
            if read(target) != data:
                raise ValueError("published conditional frontier differs")
        else:
            target.write_text(json.dumps(data, separators=(",", ":")) + "\n", encoding="utf-8")
    report = {"schema": "N26-accepted-selected-radius-conditional-frontier-partition-v1",
              "verified": True, "radius_scope": SCOPE, "source_type_acceptance_sha256": manifest["source_acceptance_sha256"],
              "source_original_U_acceptance_sha256": catalog.sha(args.input / "SOURCE-ORIGINAL-U-ACCEPTANCE.json"),
              "original_U_frontier_pending_subtrees_unchanged": len(source["pending_states"]),
              "strict_radius_conditional_terminal_paths_removed": len(paid),
              "conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
              "conditional_frontier_families": frontier["families"],
              "all_unclosed_types_boxes_siblings_and_candidate_retained": True,
              "known_candidate_unique_complete_terminal": candidate["prefix"],
              "original_U_frontier_nodes_removed": 0, "original_U_frontier_rewritten": False,
              "negative_controls_rejected": negatives,
              "full_catalog_complete": False, "global_lower_bound_proved": False,
              "global_optimality_proved": False, "n27_started": False,
              "files": {name: catalog.sha(args.input / name) for name in
                        ["MANIFEST.json", *manifest["copied_files"],
                         "RSTAR-COMPETITOR-FRONTIER.json", "CONDITIONAL-REMOVAL-LEDGER.json"]},
              "executed_checker_sha256": catalog.sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_selected_Rstar_frontier.py"]:
        raise ValueError("conditional frontier executed a different checker")
    for text, digest in original_digests.items():
        if catalog.sha(text) != digest:
            raise ValueError("conditional partition source bytes changed during replay")
    for name, digest in manifest["copied_files"].items():
        if catalog.sha(args.input / name) != digest:
            raise ValueError("conditional partition sealed input changed during replay")
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
