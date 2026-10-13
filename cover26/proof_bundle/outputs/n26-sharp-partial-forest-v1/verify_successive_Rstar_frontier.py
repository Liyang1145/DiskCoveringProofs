"""Transfer certified complete types to a separately accepted later U stage."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
from n26_force import CAPS, D
import n26_terminal_canonical as canonical
import verify_selected_Rstar_frontier as partition
from verify_selected_type_trees import SCOPE, bound, coverage_gate, publish_or_match, read
import verify_terminal_catalog as catalog


def input_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if (manifest["schema"] != "N26-successive-stage-Rstar-frontier-input-bindings-v1"
            or manifest["radius_scope"] != SCOPE):
        raise ValueError("wrong successive conditional partition scope")
    for name, digest in manifest["copied_files"].items():
        if catalog.sha(folder / name) != digest:
            raise ValueError("successive conditional partition input changed: " + name)
    inventory, reports = [], {}
    for key in ("stage", "types"):
        source = catalog.local_path(manifest["source_folders"][key])
        accepted, paths = bound(source)
        if (catalog.sha(source / "VERIFIED.json") != manifest["source_acceptance_sha256"][key]
                or read(catalog.local_path(manifest["published_replays"][key])) != accepted):
            raise ValueError("successive partition source has no matching actual published replay")
        reports[key] = accepted
        inventory.extend(paths)
        inventory.append(catalog.local_path(manifest["published_replays"][key]))
        if read(folder / ("SOURCE-" + key.upper() + "-ACCEPTANCE.json")) != accepted:
            raise ValueError("successive partition source acceptance was substituted")
    stage_folder = catalog.local_path(manifest["source_folders"]["stage"])
    types_folder = catalog.local_path(manifest["source_folders"]["types"])
    accepted, types = reports["stage"], reports["types"]
    base_partition = read(folder / "BASE-PARTITION-ACCEPTANCE.json")
    if (not base_partition["verified"] or base_partition["radius_scope"] != SCOPE
            or base_partition["global_optimality_proved"]
            or base_partition["files"]["verify_selected_Rstar_frontier.py"]
            != catalog.sha(partition.__file__)
            or base_partition["files"]["verify_selected_type_trees.py"]
            != types["files"]["verify_selected_type_trees.py"]):
        raise ValueError("successive partition changed its already accepted partition arithmetic")
    if (types["radius_scope"] != SCOPE
            or not types["all_six_selected_competitor_types_accounted_for"]
            or types["original_U_frontier_nodes_removed"] != 0
            or types["Rstar_competitor_frontier_nodes_removed_by_this_bundle"] != 0
            or not accepted["all_incoming_angle_boxes_covered"]
            or not accepted["older_forests_and_original_native_queues_preserved"]):
        raise ValueError("accepted source does not cover complete conditional or U partitions")
    source = read(stage_folder / "FRONTIER.json")
    if (source != read(folder / "SOURCE-ORIGINAL-U-FRONTIER.json")
            or catalog.sha(folder / "SOURCE-ORIGINAL-U-FRONTIER.json") != accepted["files"]["FRONTIER.json"]
            or source["families"] != accepted["families"]):
        raise ValueError("successive partition does not bind the actual later U frontier")
    native = read(stage_folder / "NATIVE-VERIFIED.json")
    for name, digest in native["files"].items():
        path = stage_folder / name
        if catalog.sha(path) != digest:
            raise ValueError("later-stage native evidence changed")
        inventory.append(path)
    for module in (partition, canonical, catalog):
        name = Path(module.__file__).name
        expected = (manifest["copied_files"][name] if name == "verify_selected_Rstar_frontier.py"
                    else types["files"][name])
        if catalog.sha(module.__file__) != expected:
            raise ValueError("successive partition imported different exact canonical arithmetic")
    for name in ("audit_prefix_origin.py", "audit_prefix_partition.py", "n26_force.py"):
        if (catalog.sha(folder / name) != accepted["files"][name]
                or catalog.sha(folder / name) != types["files"][name]):
            raise ValueError("later U and complete-type certificate use different recurrence or rods")
    catalogue = catalog.local_path(read(types_folder / "MANIFEST.json")["source_folders"]["catalog"])
    values = catalog.input_gate(catalogue)
    table = catalog.reconstruct(catalogue, *values[1:])
    if table != read(types_folder / "CATALOG-SOURCE/CATALOG.json"):
        raise ValueError("old selected canonical catalogue did not independently replay")
    inventory.append(catalogue / "VERIFIED.json")
    inventory.extend(catalogue / name for name in read(catalogue / "VERIFIED.json")["files"])
    for original, name in (("CLASSIFICATION.json", "SOURCE-CLASSIFICATION.json"),
                           ("CERTIFICATE.json", "SOURCE-TYPE-CERTIFICATE.json"),
                           ("PENDING-TYPES.json", "SOURCE-PENDING-TYPES.json"),
                           ("CANDIDATE-POSITIVE-CONTROL.json", "CANDIDATE-POSITIVE-CONTROL.json")):
        if catalog.sha(folder / name) != types["files"][original]:
            raise ValueError("successive partition changed a paid type or its unresolved boxes")
    certificate = read(folder / "SOURCE-TYPE-CERTIFICATE.json")
    candidate_group = coverage_gate(certificate["types"], table)
    classifications, pending = read(folder / "SOURCE-CLASSIFICATION.json"), read(folder / "SOURCE-PENDING-TYPES.json")
    expected = [row["group_index"] for row in certificate["types"]]
    if ([row["group_index"] for row in classifications] != expected
            or [row["group_index"] for row in pending] != expected
            or [row["group_index"] for row in classifications if row["radius_at_most_Rstar_type_excluded"]]
            != types["strict_radius_conditional_type_exclusions"]):
        raise ValueError("successive partition skipped a competitor or inflated exclusions")
    return manifest, reports, inventory, source, table, classifications, pending, values[5], candidate_group


def transfer_gate(source, table):
    """Re-resolve every exact full prefix on the new frontier before reuse."""
    refs = {b: OriginReference(26, b, "dfs", caps=CAPS, scale=D) for b in (14, 15, 16, 17)}
    states, transfer = {}, []
    for state in source["pending_states"]:
        key = (state["B"], tuple(state["prefix"]))
        if key in states:
            raise ValueError("later U partition has duplicated ownership")
        states[key] = state
    for row in table["rows"]:
        b, prefix = row["B"], tuple(row["prefix"])
        key = (b, prefix)
        if key not in states:
            raise ValueError("an old selected terminal is not explicitly retained on the new U frontier")
        state = states[key]
        ref = refs[b]
        rebuilt = ref.resolve(prefix)
        actual = {"B": b, **ref.entry(prefix, rebuilt, ref.children(rebuilt))}
        if (state != actual or rebuilt.pending or rebuilt.next_vertex != 26
                or state["terminal"] is not True or state["child_count"] != 0
                or state["faces"] != row["faces"]):
            raise ValueError("an old complete-type proof was applied to a partial or different new state")
        code = canonical.canonical(26, b, state["faces"])
        if code != row["canonical"]:
            raise ValueError("new-stage selected member no longer has the accepted canonical code")
        for mapping in code["canonical_bijections"]:
            canonical.check_bijection(26, b, state["faces"], code["faces"], mapping)
        transfer.append({"catalog_member_index": row["index"], "B": b, "prefix": list(prefix),
                         "identical_complete_state_and_faces_reconstructed": True,
                         "canonical_faces": code["faces"],
                         "canonical_bijections": code["canonical_bijections"],
                         "same_type_as_known_candidate": row["same_canonical_type_as_known_candidate"]})
    return transfer


def derive(source, table, classifications, pending, candidate):
    transfer = transfer_gate(source, table)
    frontier, ledger = partition.derive(source, table, classifications, pending, candidate)
    if len(ledger) != sum(len(row["members"]) for row in classifications
                          if row["radius_at_most_Rstar_type_excluded"]):
        raise ValueError("successive conditional partition lost a certified exact full member")
    return frontier, ledger, transfer


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    manifest, reports, inventory, source, table, classifications, pending, candidate, candidate_group = input_gate(args.input)
    source_digests = {linux(path): catalog.sha(path) for path in inventory}
    frontier, ledger, transfer = derive(source, table, classifications, pending, candidate)
    negatives = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid successive conditional partition accepted: " + label)

    first = table["rows"][0]
    key = (first["B"], first["prefix"])
    bad = deepcopy(source)
    victim = next(row for row in bad["pending_states"] if (row["B"], row["prefix"]) == key)
    victim["faces"][0] ^= 1 << 25
    reject("changed-later-stage-full-face-image", lambda: transfer_gate(bad, table))
    bad = deepcopy(source)
    victim = next(row for row in bad["pending_states"] if (row["B"], row["prefix"]) == key)
    victim["prefix"] = victim["prefix"][:-1]
    reject("type-exclusion-reused-on-ancestor-prefix", lambda: transfer_gate(bad, table))
    bad = deepcopy(source)
    bad["pending_states"] = [row for row in bad["pending_states"] if row["prefix"] != candidate["prefix"]]
    reject("candidate-lost-in-successive-stage", lambda: derive(bad, table, classifications, pending, candidate))
    bad = deepcopy(source)
    victim = next(row for row in bad["pending_states"] if (row["B"], row["prefix"]) == key)
    victim["child_count"] = 1
    reject("full-terminal-changed-to-unprocessed-subtree", lambda: transfer_gate(bad, table))
    bad = deepcopy(classifications)
    bad[0]["radius_scope"] = "unconditional-original-U"
    reject("radius-conditional-proof-promoted-to-U-empty",
           lambda: derive(source, table, bad, pending, candidate))
    bad = deepcopy(pending)
    first_paid = next(row["group_index"] for row in classifications if row["radius_at_most_Rstar_type_excluded"])
    next(row for row in bad if row["group_index"] == first_paid)["closed_OPEN_boxes"].append({"index": -1})
    reject("hidden-OPEN-in-successive-type-payment",
           lambda: derive(source, table, classifications, bad, candidate))
    for name, data in (("RSTAR-COMPETITOR-FRONTIER.json", frontier),
                       ("CONDITIONAL-REMOVAL-LEDGER.json", ledger),
                       ("COMPLETE-MEMBER-TRANSFER.json", transfer)):
        publish_or_match(args.input / name, data)
    report = {
        "schema": "N26-accepted-successive-stage-radius-conditional-frontier-v1",
        "verified": True, "radius_scope": SCOPE,
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "later_original_U_pending_subtrees": len(source["pending_states"]),
        "complete_selected_members_independently_reconstructed_on_later_stage": len(transfer),
        "canonical_codes_bijections_boundary_cycles_and_all_face_images_rechecked": True,
        "strict_radius_conditional_terminal_paths_removed": len(ledger),
        "conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "conditional_frontier_families": frontier["families"],
        "known_candidate_unique_complete_34_face_terminal": candidate["prefix"],
        "all_siblings_unclosed_types_and_all_OPEN_boxes_retained": True,
        "original_U_frontier_nodes_removed": 0, "original_U_frontier_rewritten": False,
        "negative_controls_rejected": negatives,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {name: catalog.sha(args.input / name) for name in
                  ["MANIFEST.json", *manifest["copied_files"],
                   "RSTAR-COMPETITOR-FRONTIER.json", "CONDITIONAL-REMOVAL-LEDGER.json", "COMPLETE-MEMBER-TRANSFER.json"]},
        "source_files": source_digests, "executed_checker_sha256": catalog.sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_successive_Rstar_frontier.py"]:
        raise ValueError("successive partition executed a different checker")
    for text, digest in source_digests.items():
        if catalog.sha(catalog.local_path(text)) != digest:
            raise ValueError("successive partition source changed during exact replay")
    for name, digest in manifest["copied_files"].items():
        if catalog.sha(args.input / name) != digest:
            raise ValueError("successive partition sealed input changed during replay")
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "source_files")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
