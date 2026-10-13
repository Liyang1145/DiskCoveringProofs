"""Fresh exact outer payments only on the accepted original source residual.

Every original type is scanned. All old pair-pending indices are matched to
the original outer binding stream. Actual face/center/anchor maps are checked
on EVERY still-unpaid type, including types with pending outer groups.
No claim is made about unnecessary geometric maps on already-paid types.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
import argparse
import gzip
import json
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import Catalog, sha, no_duplicate_keys
from n25_outer_search import read, publish
from audit_streamed_hierarchy import check_map
import exact_graph as exact

assert __debug__


def scan(catalog_rows, bindings, pair_pending, old_pending, groups, paid, total, pending_count, ledger, residual):
    old = next(old_pending, None)
    pair = next(pair_pending, None)
    counts, membercounts = Counter(), Counter()
    binding_count = source_count = 0
    previous_binding = -1
    started = time.monotonic()
    for index, row in catalog_rows:
        assert index == source_count
        source_count += 1
        assert old is None or old >= index
        assert pair is None or pair >= index
        binding = None
        if pair == index:
            line = bindings.readline()
            assert line, "missing original outer binding"
            binding = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert type(binding["index"]) is int and binding["index"] == index > previous_binding
            previous_binding = index
            group_id = binding["group"]
            assert type(group_id) is int and 0 <= group_id < len(groups)
            membercounts[group_id] += 1
            binding_count += 1
            pair = next(pair_pending, None)
        if old == index:
            assert binding is not None, "unpaid source type absent from original outer-selected parent"
            group_id = binding["group"]
            group = groups[group_id]
            check_map(23, 15, group, binding["map"], set(row["faces"]), 1)
            counts["unpaid_actual_face_center_anchor_maps_checked"] += 1
            if group_id in paid:
                ledger.write(json.dumps({"index": index, "group": group_id,
                                         "tree_sha256": paid[group_id]}, separators=(",", ":"))+"\n")
                counts["additional_strict_outer_types"] += 1
            else:
                residual.write(json.dumps({"index": index}, separators=(",", ":"))+"\n")
                counts["pending"] += 1
            old = next(old_pending, None)
        if source_count % 250000 == 0:
            print("N23/B15 fresh effective outer payment scan", source_count,
                  "new strict", counts["additional_strict_outer_types"], "pending", counts["pending"],
                  "seconds", round(time.monotonic()-started, 1), flush=True)
    assert source_count == total and old is pair is None
    assert not bindings.read(1), "extra original outer bindings"
    assert counts["unpaid_actual_face_center_anchor_maps_checked"] == pending_count
    assert counts["additional_strict_outer_types"]+counts["pending"] == pending_count
    assert all(membercounts[g["id"]] == g["members"] for g in groups)
    return dict(counts), binding_count


def pending_indices(path, total):
    previous = -1
    with path.open(encoding="ascii") as stream:
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            value = row["index"]
            assert type(value) is int and previous < value < total
            previous = value
            yield value


def main():
    ap = argparse.ArgumentParser()
    for name in ("dataset", "parent", "pair-maps", "outer", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    dataset, parent, pairmaps, outer, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("dataset", "parent", "pair-maps", "outer", "output"))
    assert all(path.is_relative_to(ROOT) for path in (dataset, parent, pairmaps, outer, output))
    assert not output.exists()
    parentpath = parent / "VERIFIED.json"
    accepted, mappings, recovered = map(read, (parentpath, pairmaps, outer / "VERIFIED.json"))
    assert accepted["verified"] and accepted["schema"] == "frozen-N23-B15-complete-origin-and-strict-pair-disjoint-union-v1"
    assert accepted["source_sha256"] == sha(ROOT / "merge_n23_B15_origin_pair.py")
    assert accepted["all_16790546_source_indices_partitioned_once"]
    assert accepted["all_5690_positive_pair_force_trees_fresh_replayed_again"]
    assert accepted["old_strict_and_origin_overlap_deducted_not_double_counted"]
    assert (accepted["N"], accepted["B"], accepted["catalog_types"]) == (23, 15, 16790546)
    for path, digest in accepted["frozen_files"].items():
        assert sha(path) == digest
    assert mappings["verified"] and mappings["source_sha256"] == sha(HIGH / "audit_streamed_hierarchy.py")
    assert mappings["disjoint_hierarchy_partition_verified"] and mappings["catalog_types"] == 16790546
    assert mappings["catalog_sha256"] == accepted["catalog_sha256"]
    assert len(mappings["stages"]) == 1 and mappings["pending_types"] == 13603249
    assert recovered["verified"] and recovered["schema"] == "isolated-N23-relevant-original-outer-tree-recovery-and-replay-v1"
    assert recovered["source_sha256"] == sha(ROOT / "recover_n23_B15_effective_outer_trees.py")
    assert recovered["strict_trees_recovered_and_fresh_replayed"] == 22857
    groupspath, receiptpath, replaypath = (
        outer / "OUTER/GROUPS.json", outer / "FORCE/SUMMARY.json", outer / "EXACT-REPLAY.json")
    data, receipt, replay = map(read, (groupspath, receiptpath, replaypath))
    groups = data["groups"]
    digest = sha(groupspath)
    assert digest == recovered["groups_sha256"] == receipt["groups_sha256"] == replay["groups_sha256"]
    assert (data["N"], data["B"], data["threshold"], data["group_count"]) == (23, 15, 1, 535262)
    assert data["parent_groups_sha256"] == sha(dataset / "PAIR/GROUPS.json")
    assert data["parent_proof_sha256"] == sha(
        ROOT / "n23-B15-original5690-pair-force-tree-recovery-20261005-v1/SUMMARY.json")
    assert replay["verified"] and replay["receipt_sha256"] == recovered["receipt_sha256"] == sha(receiptpath)
    assert recovered["exact_replay_sha256"] == sha(replaypath)
    assert replay["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert receipt["source_sha256"] == sha(ROOT / "recover_n23_B15_effective_outer_trees.py")
    assert receipt["schema"] == "filtered-original-logged-N23-outer-positive-tree-receipt-v1"
    assert [row["group"] for row in receipt["outcomes"]] == list(range(535262))
    assert [g["id"] for g in groups] == list(range(535262))
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    constants = read(constants_path)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    constantshash = sha(constants_path)
    files = {}
    paid = {}
    for group, outcome in zip(groups, receipt["outcomes"], strict=True):
        assert outcome["status"] in ("excluded", "pending")
        if outcome["status"] == "pending":
            continue
        assert 15 <= group["centers"] < 23
        treepath = outer / f"FORCE/group-{group['id']:07}.json.gz"
        assert sha(treepath) == outcome["tree_sha256"]
        with gzip.open(treepath, "rt", encoding="utf8") as source:
            tree = json.load(source, object_pairs_hook=no_duplicate_keys)
        assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
            23, 15, group["centers"], group["faces"])
        assert tree["groups_sha256"] == digest and tree["constants_sha256"] == constantshash
        assert tree["radius_upper"] == constants["radius_upper"]
        result = exact.verify(15, group["centers"], group["faces"], tree["nodes"], constants)
        assert result["verified"] and result["nodes"] == outcome["nodes"] and result["counts"] == outcome["counts"]
        assert F(result["minimum_force_margin"]) > 0 and outcome["members"] == group["members"]
        paid[group["id"]] = sha(treepath)
        files[str(treepath)] = sha(treepath)
        if len(paid) % 2000 == 0:
            print("Effective original outer strict trees freshly replayed again", len(paid), "/22857", flush=True)
    assert len(paid) == receipt["excluded_groups"] == replay["exact_groups_replayed"] == 22857
    catalogpath = dataset / "CATALOG/N23-B15-dfs.json"
    oldpendingpath = parent / "PENDING.jsonl"
    pairpendingpath = pairmaps.parent / mappings["pending_indices_file"]
    bindingspath = outer / "OUTER/bindings.jsonl"
    assert sha(catalogpath) == accepted["catalog_sha256"]
    assert sha(oldpendingpath) == accepted["pending_sha256"]
    assert sha(pairpendingpath) == mappings["pending_indices_sha256"]
    assert sha(bindingspath) == data["bindings_sha256"] == replay["bindings_sha256"]
    assert data["selected_types"] == 13603249 and data["catalog_types"] == 16790546
    for path in (
        Path(__file__).resolve(), parentpath, oldpendingpath, pairmaps, pairpendingpath,
        outer / "VERIFIED.json", groupspath, receiptpath, replaypath, bindingspath, catalogpath,
        HIGH / "exact_graph.py", HIGH / "audit_streamed_hierarchy.py", HIGH / "stream_catalog.py", constants_path):
        files[str(path)] = sha(path)
    output.mkdir()
    catalog = Catalog(catalogpath)
    with bindingspath.open(encoding="ascii") as bindings, \
            (output / "ADDITIONAL-PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as residual:
        counts, bound_count = scan(
            catalog.rows(), bindings, pending_indices(pairpendingpath, 16790546),
            pending_indices(oldpendingpath, 16790546), groups, paid,
            16790546, accepted["pending_full_types"], ledger, residual)
    assert catalog.finished and bound_count == data["selected_types"]
    for path, digest in files.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath", "group_catalog"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-N23-B15-origin-pair-and-effective-outer-disjoint-payment-v1",
        "N": 23, "B": 15, "original_catalog_types": 16790546,
        "previous_pending_full_types": accepted["pending_full_types"],
        "additional_strict_outer_types": counts["additional_strict_outer_types"],
        "pending_full_types": counts["pending"],
        "all_original_source_rows_and_complete_end_of_file_checked": True,
        "all_old_pair_pending_indices_match_original_outer_binding_indices": True,
        "original_outer_group_member_counts_freshly_scanned": True,
        "all_previous_unpaid_source_face_center_anchor_maps_independently_checked": True,
        "all_22857_positive_outer_trees_freshly_exact_replayed_again": True,
        "old_paid_source_types_not_recounted": True,
        "unnecessary_actual_geometry_maps_for_already_paid_types_not_claimed": True,
        "original_outer_binding_rows": bound_count,
        "parent_payment_report_sha256": sha(parentpath),
        "additional_payments_sha256": sha(output / "ADDITIONAL-PAYMENTS.jsonl"),
        "pending_sha256": sha(output / "PENDING.jsonl"),
        "frozen_files": files, "source_sha256": sha(Path(__file__)),
        "historical_catalog_completeness_and_arbitrary_cover_transport_still_upstream": True,
        "all_remaining_type_lower_bounds_other_boundary_families_and_exact_upper_still_required": True,
        "global_optimality_proved": False,
    })
    print("Complete-source effective outer payment independently accepted:", counts, flush=True)


if __name__ == "__main__":
    main()
