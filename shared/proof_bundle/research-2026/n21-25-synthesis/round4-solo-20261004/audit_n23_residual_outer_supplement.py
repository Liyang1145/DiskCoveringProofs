"""Independent exact new trees and original residual type maps; no recount.

The all-source/map scanner is the already-controlled frozen stdlib scanner.
The new proposal stage must have ended and independently replayed its receipt.
Previous payments remain upstream; only exact old pending indices can be added.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import Catalog, sha, no_duplicate_keys
from n25_outer_search import read, publish
from audit_n23_B15_effective_outer_payment import scan, pending_indices
import exact_graph as exact

assert __debug__


def fresh_tree(group, outcome, tree, digest, constantshash, constants):
    assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
        23, 15, group["centers"], group["faces"])
    assert tree["groups_sha256"] == digest and tree["constants_sha256"] == constantshash
    assert tree["radius_upper"] == constants["radius_upper"]
    result = exact.verify(15, group["centers"], group["faces"], tree["nodes"], constants)
    assert result["verified"] and F(result["minimum_force_margin"]) > 0
    assert (result["nodes"], result["counts"]) == (outcome["nodes"], outcome["counts"])
    assert group["members"] == outcome["members"]
    return result


def main():
    ap = argparse.ArgumentParser()
    for name in ("dataset", "parent", "pair-maps", "outer", "stage", "controls", "tree-controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    dataset, parent, pairmaps, outer, stage, controlpath, treecontrolpath, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("dataset", "parent", "pair-maps", "outer", "stage", "controls", "tree-controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (
        dataset, parent, pairmaps, outer, stage, controlpath, treecontrolpath, output))
    assert not output.exists()
    accepted, mappings, controls = map(read, (parent / "VERIFIED.json", pairmaps, controlpath))
    assert accepted["verified"]
    assert accepted["schema"] == "complete-N23-B15-origin-pair-and-effective-outer-disjoint-payment-v1"
    assert accepted["source_sha256"] == sha(ROOT / "audit_n23_B15_effective_outer_payment.py")
    assert accepted["all_previous_unpaid_source_face_center_anchor_maps_independently_checked"]
    assert accepted["all_22857_positive_outer_trees_freshly_exact_replayed_again"]
    assert accepted["pending_full_types"] == 793841
    assert controls["verified"] and controls["schema"] == "N23-effective-outer-full-source-payment-finite-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n23_effective_outer_payment.py")
    assert controls["audit_source_sha256"] == sha(ROOT / "audit_n23_B15_effective_outer_payment.py")
    assert len(controls["negative_controls_rejected"]) == 14
    treecontrols = read(treecontrolpath)
    assert treecontrols["verified"] and treecontrols["schema"] == "N23-residual-new-tree-identity-controls-v1"
    assert treecontrols["audit_source_sha256"] == sha(Path(__file__))
    assert treecontrols["source_sha256"] == sha(ROOT / "test_n23_residual_outer_trees.py")
    assert mappings["verified"] and mappings["source_sha256"] == sha(HIGH / "audit_streamed_hierarchy.py")
    assert mappings["disjoint_hierarchy_partition_verified"]
    assert len(mappings["stages"]) == 1 and mappings["pending_types"] == 13603249
    files = dict(accepted["frozen_files"])
    for path, digest in files.items():
        assert sha(path) == digest
    groupspath, bindingspath, previouspath = (
        outer / "OUTER/GROUPS.json", outer / "OUTER/bindings.jsonl", outer / "FORCE/SUMMARY.json")
    assert all(files[str(path)] == sha(path) for path in (groupspath, bindingspath, previouspath))
    data, previous = read(groupspath), read(previouspath)
    digest = sha(groupspath)
    assert previous["groups_sha256"] == digest and previous["excluded_groups"] == 22857
    assert (data["N"], data["B"], data["threshold"], data["group_count"]) == (23, 15, 1, 535262)
    assert [g["id"] for g in data["groups"]] == list(range(535262))
    assert [r["group"] for r in previous["outcomes"]] == list(range(535262))
    assert data["bindings_sha256"] == sha(bindingspath)
    receiptpath, replaypath, inputpath = (
        stage / "SUMMARY.json", stage / "EXACT-REPLAY.json", stage / "INPUT-SNAPSHOT.json")
    receipt, replay, inputs = map(read, (receiptpath, replaypath, inputpath))
    assert receipt["source_sha256"] == sha(ROOT / "probe_n23_remaining_outer_v2.py")
    assert receipt["requested_groups_complete"] and receipt["all_unselected_original_groups_explicitly_pending"]
    assert receipt["groups_sha256"] == replay["groups_sha256"] == digest
    assert receipt["known_attaining_group_control"] == inputs["known_attaining_original_group"] == 522460
    assert receipt["known_attaining_group_original_member_count"] == inputs["known_attaining_members"] == 169
    assert inputs["selected_group_count"] == len(inputs["selected_original_groups"]) == 6879
    selected = set(inputs["selected_original_groups"])
    assert len(selected) == 6879
    actual_selected = {g["id"] for g, r in zip(data["groups"], previous["outcomes"], strict=True)
                       if g["centers"] < 23 and r["status"] == "pending"}
    assert selected == actual_selected
    assert sum(data["groups"][gid]["members"] for gid in selected) == accepted["pending_full_types"]
    for path, expected in receipt["frozen_files"].items():
        assert sha(path) == expected
        files[path] = expected
    assert replay["verified"] and replay["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert replay["receipt_sha256"] == sha(receiptpath) and replay["bindings_sha256"] == sha(bindingspath)
    terminal = read(stage / "REPLAY-TERMINAL.json")
    assert terminal["independent_process_terminal_observed"] and terminal["actual_exit_code"] == 0
    assert terminal["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n23.json"
    constants, constantshash = read(constants_path), sha(constants_path)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    assert [r["group"] for r in receipt["outcomes"]] == list(range(535262))
    paid, members = {}, 0
    for group, outcome in zip(data["groups"], receipt["outcomes"], strict=True):
        assert outcome["status"] in ("excluded", "pending")
        if outcome["status"] == "pending":
            continue
        gid = group["id"]
        assert gid in selected and gid != 522460
        assert previous["outcomes"][gid]["status"] == "pending" and 15 <= group["centers"] < 23
        treepath = stage / f"group-{gid:07}.json.gz"
        assert sha(treepath) == outcome["tree_sha256"]
        with gzip.open(treepath, "rt", encoding="utf8") as stream:
            tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
        fresh_tree(group, outcome, tree, digest, constantshash, constants)
        paid[gid] = outcome["tree_sha256"]
        members += group["members"]
        files[str(treepath)] = outcome["tree_sha256"]
        if len(paid) % 500 == 0:
            print("N23 residual new trees freshly replayed again", len(paid), flush=True)
    assert len(paid) == receipt["excluded_groups"] == replay["exact_groups_replayed"]
    assert members == receipt["catalog_members_excluded"] == replay["associated_member_count"]
    catalogpath, pendingpath = dataset / "CATALOG/N23-B15-dfs.json", parent / "PENDING.jsonl"
    pairpendingpath = pairmaps.parent / mappings["pending_indices_file"]
    assert sha(catalogpath) == mappings["catalog_sha256"] == files[str(catalogpath)]
    assert sha(pendingpath) == accepted["pending_sha256"]
    assert sha(pairpendingpath) == mappings["pending_indices_sha256"] == files[str(pairpendingpath)]
    output.mkdir()
    catalog = Catalog(catalogpath)
    with bindingspath.open(encoding="ascii") as bindings, \
            (output / "ADDITIONAL-PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as residual:
        counts, binding_count = scan(
            catalog.rows(), bindings, pending_indices(pairpendingpath, 16790546),
            pending_indices(pendingpath, 16790546), data["groups"], paid,
            16790546, accepted["pending_full_types"], ledger, residual)
    assert catalog.finished and binding_count == data["selected_types"] == 13603249
    for path in (Path(__file__), parent / "VERIFIED.json", pendingpath, pairmaps, controlpath, treecontrolpath,
                 groupspath, bindingspath, previouspath, receiptpath, replaypath, inputpath,
                 stage / "REPLAY-TERMINAL.json", catalogpath, constants_path,
                 HIGH / "exact_graph.py", Path(exact.kernel.__file__),
                 ROOT / "audit_n23_B15_effective_outer_payment.py"):
        files[str(path.resolve())] = sha(path)
    for path, expected in files.items():
        assert sha(path) == expected
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath", "group_catalog"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "original-N23-B15-residual-outer-fresh-supplement-payment-v1",
        "N": 23, "B": 15, "original_catalog_types": 16790546,
        "previous_pending_full_types": accepted["pending_full_types"],
        "additional_strict_outer_types": counts["additional_strict_outer_types"],
        "pending_full_types": counts["pending"], "new_positive_groups_freshly_replayed": len(paid),
        "all_source_indices_and_original_outer_bindings_scanned": True,
        "every_previous_unpaid_actual_face_center_anchor_map_freshly_checked": True,
        "all_new_positive_trees_independently_freshly_exact_replayed_again": True,
        "only_previous_pending_source_types_paid_no_prior_payment_recount": True,
        "known_attaining_outer_group_explicitly_retained": 522460,
        "unnecessary_geometry_maps_on_already_paid_types_not_claimed": True,
        "parent_payment_report_sha256": sha(parent / "VERIFIED.json"),
        "additional_payments_sha256": sha(output / "ADDITIONAL-PAYMENTS.jsonl"),
        "pending_sha256": sha(output / "PENDING.jsonl"),
        "frozen_files": files, "source_sha256": sha(Path(__file__)),
        "remaining_type_lower_bounds_source_transport_other_families_and_exact_upper_still_required": True,
        "global_optimality_proved": False,
    })
    print("N23 residual full-source supplement independently accepted:", counts, flush=True)


if __name__ == "__main__":
    main()
