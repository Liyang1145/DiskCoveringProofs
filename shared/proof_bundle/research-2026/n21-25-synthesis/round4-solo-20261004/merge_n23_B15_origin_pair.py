"""Fresh force replay and disjoint union of two full-byte-catalog partitions."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
import exact_graph as exact

assert __debug__


def indices(stream, total):
    previous = -1
    for line in stream:
        row = json.loads(line, object_pairs_hook=no_duplicate_keys)
        index = row["index"]
        assert type(index) is int and previous < index < total, "invalid, duplicate, or unordered index"
        previous = index
        yield index


def merge_indices(origin, pair, total, expected_origin_pending, expected_pair_pending, residual):
    left, right = next(origin, None), next(pair, None)
    counts = Counter()
    left_seen = right_seen = 0
    for index in range(total):
        assert left is None or left >= index
        assert right is None or right >= index
        origin_pending, pair_pending = left == index, right == index
        if not origin_pending:
            counts["actual-cover-origin-obstruction"] += 1
            if not pair_pending:
                counts["overlap_not_counted_twice"] += 1
        elif not pair_pending:
            counts["additional-strict-pair-force"] += 1
        else:
            counts["pending"] += 1
            residual.write(json.dumps({"index": index}, separators=(",", ":"))+"\n")
        if origin_pending:
            left_seen += 1
            left = next(origin, None)
        if pair_pending:
            right_seen += 1
            right = next(pair, None)
    assert left is right is None, "extra partition indices"
    assert left_seen == expected_origin_pending and right_seen == expected_pair_pending
    assert (counts["actual-cover-origin-obstruction"]+
            counts["additional-strict-pair-force"]+counts["pending"]) == total
    return dict(counts)


def main():
    ap = argparse.ArgumentParser()
    for name in ("dataset", "origin", "pair-maps", "pair-force", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    dataset, origin, pairmaps, pairforce, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("dataset", "origin", "pair-maps", "pair-force", "output"))
    assert all(path.is_relative_to(ROOT) for path in (dataset, origin, pairmaps, pairforce, output))
    assert not output.exists()
    originpath = origin / "ACCEPTED/VERIFIED.json"
    origins = read(originpath)
    assert origins["verified"] and origins["schema"] == "independent-frozen-N23-B15-full-type-origin-partition-v1"
    assert origins["source_sha256"] == sha(ROOT / "audit_n23_B15_origin_catalog.py")
    assert origins["all_16790546_declared_rows_fresh_stream_scanned"]
    assert origins["all_obstruction_and_pending_indices_partitioned_once"]
    assert origins["all_exposure_masks_independently_recomputed_from_actual_faces"]
    assert origins["source_end_of_file_and_declared_orbit_count_checked"]
    N, B, total = origins["N"], origins["B"], origins["catalog_types_scanned"]
    assert (N, B, total) == (23, 15, 16790546)
    files = dict(origins["frozen_files"])
    for path, digest in files.items():
        assert sha(path) == digest
    catalogpath = dataset / "CATALOG/N23-B15-dfs.json"
    assert origins["catalog_sha256"] == sha(catalogpath)
    mappings = read(pairmaps)
    assert mappings["verified"] and mappings["source_sha256"] == sha(HIGH / "audit_streamed_hierarchy.py")
    assert mappings["stream_reader_sha256"] == sha(HIGH / "stream_catalog.py")
    assert mappings["disjoint_hierarchy_partition_verified"]
    assert (mappings["N"], mappings["B"], mappings["catalog_types"]) == (N, B, total)
    assert mappings["catalog_sha256"] == origins["catalog_sha256"]
    assert len(mappings["stages"]) == 1
    stage = mappings["stages"][0]
    groupfile, receiptpath, replaypath = (
        dataset / "PAIR/GROUPS.json", pairforce / "SUMMARY.json", pairforce / "EXACT-REPLAY.json")
    groups, receipt, replay = map(read, (groupfile, receiptpath, replaypath))
    groupdigest = sha(groupfile)
    assert stage["groups_sha256"] == receipt["groups_sha256"] == replay["groups_sha256"] == groupdigest
    assert stage["force_replay_sha256"] == sha(replaypath) and replay["receipt_sha256"] == sha(receiptpath)
    assert stage["bindings_sha256"] == groups["bindings_sha256"] == sha(dataset / "PAIR/bindings.jsonl")
    assert stage["maps_checked"] == groups["selected_types"] == total and stage["threshold"] == 2
    assert receipt["source_sha256"] == sha(HIGH / "probe_groups.py")
    assert replay["verified"] and replay["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert len(receipt["outcomes"]) == groups["group_count"] == len(groups["groups"]) == 20139
    assert [row["group"] for row in receipt["outcomes"]] == list(range(20139))
    constantspath = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    constants = read(constantspath)
    assert constants["verified"] and constants["N"] == N
    assert F(constants["radius_upper"]) == F(origins["radius_upper"]) < F(1, 4)
    constantshash = sha(constantspath)
    accepted = members = 0
    for group, outcome in zip(groups["groups"], receipt["outcomes"], strict=True):
        assert outcome["status"] in ("excluded", "pending")
        if outcome["status"] == "pending":
            continue
        treepath = pairforce / f"group-{group['id']:07}.json.gz"
        assert sha(treepath) == outcome["tree_sha256"]
        with gzip.open(treepath, "rt", encoding="utf8") as stream:
            tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
        assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
            N, B, group["centers"], group["faces"])
        assert tree["groups_sha256"] == groupdigest and tree["constants_sha256"] == constantshash
        assert tree["radius_upper"] == constants["radius_upper"]
        result = exact.verify(B, group["centers"], group["faces"], tree["nodes"], constants)
        assert result["verified"] and result["nodes"] == outcome["nodes"] and result["counts"] == outcome["counts"]
        assert F(result["minimum_force_margin"]) > 0 and outcome["members"] == group["members"]
        members += group["members"]
        accepted += 1
        files[str(treepath)] = sha(treepath)
    assert accepted == receipt["excluded_groups"] == replay["exact_groups_replayed"] == 5690
    assert members == receipt["catalog_members_excluded"] == stage["paid_types"] == 3187297
    assert total-members == mappings["pending_types"] == stage["remaining_types"]
    originpending, pairpending = origin / "PENDING.jsonl", pairmaps.parent / mappings["pending_indices_file"]
    assert origins["pending_sha256"] == sha(originpending)
    assert mappings["pending_indices_sha256"] == sha(pairpending)
    output.mkdir()
    residualpath = output / "PENDING.jsonl"
    with originpending.open(encoding="ascii") as source, pairpending.open(encoding="utf8") as pair_source, \
            residualpath.open("x", encoding="ascii") as residual:
        header = json.loads(next(source), object_pairs_hook=no_duplicate_keys)
        assert header["N"] == N and header["B"] == B and header["catalog_sha256"] == origins["catalog_sha256"]
        assert header["kind"] == "not-paid-by-origin-condition"
        counts = merge_indices(indices(source, total), indices(pair_source, total), total,
                               origins["pending_full_types"], mappings["pending_types"], residual)
    assert counts["actual-cover-origin-obstruction"] == origins["actual_cover_origin_obstructions"]
    assert counts["additional-strict-pair-force"]+counts.get("overlap_not_counted_twice", 0) == members
    for path in (
        Path(__file__).resolve(), originpath, originpending, pairmaps, pairpending,
        groupfile, receiptpath, replaypath, constantspath, dataset / "PAIR/bindings.jsonl",
        HIGH / "audit_streamed_hierarchy.py", HIGH / "exact_graph.py", HIGH / "stream_catalog.py"):
        files[str(path)] = sha(path)
    for path, digest in files.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "frozen-N23-B15-complete-origin-and-strict-pair-disjoint-union-v1",
        "N": N, "B": B, "catalog_types": total, "payment_counts": counts,
        "pending_full_types": counts.get("pending", 0),
        "all_16790546_source_indices_partitioned_once": True,
        "all_5690_positive_pair_force_trees_fresh_replayed_again": True,
        "all_original_pair_maps_freshly_accepted_by_frozen_hierarchy_audit": True,
        "old_strict_and_origin_overlap_deducted_not_double_counted": True,
        "catalog_sha256": origins["catalog_sha256"], "pending_sha256": sha(residualpath),
        "frozen_files": files, "source_sha256": sha(Path(__file__)),
        "actual_cover_origin_condition_not_standalone_graph_geometry": True,
        "historical_catalog_completeness_and_arbitrary_cover_transport_still_upstream": True,
        "other_boundary_families_and_remaining_lower_bounds_still_required": True,
        "global_optimality_proved": False,
    })
    print("N23/B15 all-source origin/pair disjoint union accepted:", counts, flush=True)


if __name__ == "__main__":
    main()
