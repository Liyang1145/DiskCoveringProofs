"""Exact strict-library and all-row finite slab replay; no native code or solver."""
from pathlib import Path
from collections import Counter
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from group_catalog import validate
from family_sparse_gate import sparse_library_gate
from n25_outer_search import read, publish, bind, unchanged
from closed_origin_slab import rows, ledger_header

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--proposal", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    args.proposal, args.output = args.proposal.resolve(), args.output.resolve()
    assert args.proposal.is_relative_to(ROOT) and args.output.is_relative_to(ROOT)
    assert not args.output.exists()
    proposal = read(args.proposal)
    assert proposal["schema"] == "finite-closed-origin-slab-sparse-partition-proposal-v1"
    assert proposal["source_sha256"] == sha(ROOT / "pay_closed_origin_slab.py")
    assert proposal["not_a_complete_competitor_family_or_union"]
    assert proposal["row_numbers_are_local_to_this_hash_bound_slab_not_final_union_ids"]
    assert proposal["N"] == 25 and proposal["B"] in (15, 16, 17)
    B, slab_index = proposal["B"], proposal["slab_index"]
    source_slab = (ROOT / proposal["source_slab_relative_to_round4"]).resolve()
    library_path = (ROOT / proposal["library_relative_to_round4"]).resolve()
    assert source_slab.is_relative_to(ROOT) and library_path.is_relative_to(ROOT)
    assert sha(source_slab) == proposal["source_slab_sha256"]
    assert sha(library_path) == proposal["library_sha256"]
    ledger, pending = args.proposal.parent / "PARTITION.jsonl", args.proposal.parent / "PENDING.jsonl"
    assert sha(ledger) == proposal["partition_sha256"] and sha(pending) == proposal["pending_sha256"]
    constants, library, table, files = sparse_library_gate(library_path)
    assert library["B"] == B
    unchanged(proposal["files_relative_to_workspace"])
    files.update(proposal["files_relative_to_workspace"])
    obstacles = {o["id"]: o for o in library["obstacles"]}
    totals, obstacle_counts = Counter(), Counter()
    with ledger.open(encoding="ascii") as payments, pending.open(encoding="ascii") as residual:
        expected_header = ledger_header(25, B, slab_index)
        for stream in (payments, residual):
            assert json.loads(next(stream), object_pairs_hook=no_duplicate_keys) == expected_header
        for index, row in rows(source_slab, B, slab_index):
            entry = json.loads(next(payments), object_pairs_hook=no_duplicate_keys)
            assert entry["slab_row"] == index
            assert (entry["centers"], entry["faces"]) == (row["centers"], row["faces"])
            if entry["status"] == "strict-sparse-injection":
                assert set(entry) == {"slab_row", "centers", "faces", "status", "obstacle", "map"}
                assert type(entry["obstacle"]) is int and entry["obstacle"] in obstacles
                obstacle = obstacles[entry["obstacle"]]
                assert len(entry["map"]["centers"]) == obstacle["centers"]
                assert len(entry["map"]["anchors"]) == B
                validate(row["centers"], B, obstacle["faces"], entry["map"], row["faces"])
                obstacle_counts[entry["obstacle"]] += 1
            else:
                assert entry["status"] == "pending" and entry["no_match_is_not_an_exclusion"]
                assert set(entry) == {"slab_row", "centers", "faces", "status", "no_match_is_not_an_exclusion"}
                assert json.loads(next(residual), object_pairs_hook=no_duplicate_keys) == entry
            totals[entry["status"]] += 1
        assert not payments.read().strip() and not residual.read().strip()
    assert sum(totals.values()) == proposal["finite_rows"] == 100000
    assert totals["strict-sparse-injection"] == proposal["strictly_paid_rows"]
    assert totals["pending"] == proposal["pending_rows"]
    for path in (Path(__file__), args.proposal, library_path, source_slab, ledger, pending):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath",
                                                   "pay_closed_origin_slab", "verify_sparse_maps_fast"))
    publish(args.output, {
        "verified": True, "schema": "independent-finite-origin-slab-sparse-partition-v1",
        "N": 25, "B": B, "slab_index": slab_index, "finite_rows_fully_scanned": 100000,
        "strictly_paid_rows": totals["strict-sparse-injection"], "pending_rows": totals["pending"],
        "payments_by_obstacle": dict(obstacle_counts),
        "all_source_library_trees_fresh_exact_replayed": True,
        "all_source_rows_and_positive_center_anchor_face_maps_checked": True,
        "all_finite_source_rows_partitioned_exactly_once": True,
        "all_unmatched_rows_preserved_unpaid": True,
        "no_optimizer_native_matcher_or_proposer_used_in_replay": True,
        "source_slab_sha256": sha(source_slab), "library_sha256": sha(library_path),
        "partition_sha256": sha(ledger), "pending_sha256": sha(pending),
        "proposal_sha256": sha(args.proposal), "source_sha256": sha(Path(__file__)),
        "files_relative_to_workspace": files,
        "row_numbers_are_local_to_this_hash_bound_slab_not_final_union_ids": True,
        "not_a_complete_competitor_family_or_union": True,
        "global_optimality_proved": False,
    })
    print("Independent finite closed-slab replay PASS:",
          totals["strict-sparse-injection"], "strict;", totals["pending"], "pending", flush=True)


if __name__ == "__main__":
    main()
