"""Iterative fresh strict-tree/residual-type transport on a verified N23 parent."""
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
from audit_n23_residual_outer_supplement import fresh_tree
import exact_graph as exact

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("dataset", "parent", "pair-maps", "outer", "stage", "proposal-source",
                 "map-controls", "tree-controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    dataset, parent, pairmaps, outer, stage, proposalsource, mapcontrolpath, treecontrolpath, output = (
        getattr(args, name.replace("-", "_")).resolve() for name in (
            "dataset", "parent", "pair-maps", "outer", "stage", "proposal-source",
            "map-controls", "tree-controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (
        dataset, parent, pairmaps, outer, stage, proposalsource, mapcontrolpath, treecontrolpath, output))
    assert not output.exists()
    accepted, mappings, mapcontrols, treecontrols = map(
        read, (parent / "VERIFIED.json", pairmaps, mapcontrolpath, treecontrolpath))
    assert accepted["verified"] and (accepted["N"], accepted["B"]) == (23, 15)
    assert accepted["schema"] in (
        "original-N23-B15-residual-outer-fresh-supplement-payment-v1",
        "iterative-original-N23-B15-residual-outer-strict-payment-v1")
    assert accepted["source_sha256"] in (
        sha(ROOT / "audit_n23_residual_outer_supplement.py"), sha(Path(__file__)))
    assert accepted["all_source_indices_and_original_outer_bindings_scanned"]
    assert accepted["every_previous_unpaid_actual_face_center_anchor_map_freshly_checked"]
    assert accepted["only_previous_pending_source_types_paid_no_prior_payment_recount"]
    assert accepted["original_catalog_types"] == 16790546
    assert 0 < accepted["pending_full_types"] < 793841
    assert mapcontrols["verified"] and mapcontrols["schema"] == "N23-effective-outer-full-source-payment-finite-controls-v1"
    assert mapcontrols["audit_source_sha256"] == sha(ROOT / "audit_n23_B15_effective_outer_payment.py")
    assert mapcontrols["source_sha256"] == sha(ROOT / "test_n23_effective_outer_payment.py")
    assert treecontrols["verified"] and treecontrols["schema"] == "N23-residual-new-tree-identity-controls-v1"
    assert treecontrols["audit_source_sha256"] == sha(ROOT / "audit_n23_residual_outer_supplement.py")
    assert treecontrols["source_sha256"] == sha(ROOT / "test_n23_residual_outer_trees.py")
    assert mappings["verified"] and mappings["source_sha256"] == sha(HIGH / "audit_streamed_hierarchy.py")
    assert mappings["disjoint_hierarchy_partition_verified"]
    assert mappings["pending_types"] == 13603249 and len(mappings["stages"]) == 1
    files = dict(accepted["frozen_files"])
    for path, digest in files.items():
        assert sha(path) == digest
    groupspath, bindingspath = outer / "OUTER/GROUPS.json", outer / "OUTER/bindings.jsonl"
    assert sha(groupspath) == files[str(groupspath)]
    assert sha(bindingspath) == files[str(bindingspath)]
    data = read(groupspath)
    digest = sha(groupspath)
    assert (data["N"], data["B"], data["threshold"], data["group_count"]) == (23, 15, 1, 535262)
    assert [g["id"] for g in data["groups"]] == list(range(535262))
    receiptpath, replaypath, inputpath, terminalpath = (
        stage / name for name in ("SUMMARY.json", "EXACT-REPLAY.json", "INPUT-SNAPSHOT.json", "REPLAY-TERMINAL.json"))
    receipt, replay, inputs, terminal = map(read, (receiptpath, replaypath, inputpath, terminalpath))
    assert receipt["source_sha256"] == sha(proposalsource) and receipt["requested_groups_complete"]
    assert (receipt["N"], receipt["B"]) == (23, 15)
    assert receipt["groups_sha256"] == replay["groups_sha256"] == digest
    assert receipt["known_attaining_group_control"] == inputs["known_attaining_original_group"] == 522460
    assert inputs["known_attaining_members"] == data["groups"][522460]["members"] == 169
    assert inputs["previous_6772_positive_groups_not_reproposed"]
    selected = set(inputs["selected_original_groups"])
    assert len(selected) == len(inputs["selected_original_groups"]) == inputs["selected_group_count"]
    assert receipt["selected_original_group_count"] == len(selected)
    assert 522460 in selected and all(type(gid) is int and 0 <= gid < 535262 for gid in selected)
    assert sum(data["groups"][gid]["members"] for gid in selected) == accepted["pending_full_types"]
    for path, expected in receipt["frozen_files"].items():
        assert sha(path) == expected
        files[path] = expected
    assert replay["verified"] and replay["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert replay["receipt_sha256"] == sha(receiptpath) and replay["bindings_sha256"] == sha(bindingspath)
    assert terminal["independent_process_terminal_observed"] and terminal["actual_exit_code"] == 0
    assert terminal["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    constantspath = HIGH.parent / "evidence/core-reduction/constants/n23.json"
    constants, constantshash = read(constantspath), sha(constantspath)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    assert [row["group"] for row in receipt["outcomes"]] == list(range(535262))
    paid, members = {}, 0
    for group, outcome in zip(data["groups"], receipt["outcomes"], strict=True):
        assert outcome["status"] in ("excluded", "pending")
        if outcome["status"] == "pending":
            continue
        gid = group["id"]
        assert gid in selected and gid != 522460 and group["centers"] < 23
        treepath = stage / f"group-{gid:07}.json.gz"
        assert sha(treepath) == outcome["tree_sha256"]
        with gzip.open(treepath, "rt", encoding="utf8") as source:
            tree = json.load(source, object_pairs_hook=no_duplicate_keys)
        fresh_tree(group, outcome, tree, digest, constantshash, constants)
        paid[gid] = outcome["tree_sha256"]
        files[str(treepath)] = outcome["tree_sha256"]
        members += group["members"]
    assert len(paid) == receipt["excluded_groups"] == replay["exact_groups_replayed"]
    assert members == receipt["catalog_members_excluded"] == replay["associated_member_count"]
    catalogpath, pendingpath = dataset / "CATALOG/N23-B15-dfs.json", parent / "PENDING.jsonl"
    pairpendingpath = pairmaps.parent / mappings["pending_indices_file"]
    assert pairpendingpath.is_relative_to(ROOT)
    assert sha(catalogpath) == mappings["catalog_sha256"] == files[str(catalogpath)]
    assert sha(pairpendingpath) == mappings["pending_indices_sha256"] == files[str(pairpendingpath)]
    assert sha(pendingpath) == accepted["pending_sha256"]
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
    for path in (Path(__file__), parent / "VERIFIED.json", pendingpath, pairmaps, proposalsource,
                 mapcontrolpath, treecontrolpath, groupspath, bindingspath, receiptpath,
                 replaypath, inputpath, terminalpath, catalogpath, constantspath,
                 ROOT / "audit_n23_B15_effective_outer_payment.py",
                 ROOT / "audit_n23_residual_outer_supplement.py", HIGH / "exact_graph.py",
                 Path(exact.kernel.__file__)):
        files[str(path.resolve())] = sha(path)
    for path, digest in files.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath", "group_catalog"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "iterative-original-N23-B15-residual-outer-strict-payment-v1",
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
    print("Iterative N23 full-source residual strict payment independently accepted:", counts, flush=True)


if __name__ == "__main__":
    main()
