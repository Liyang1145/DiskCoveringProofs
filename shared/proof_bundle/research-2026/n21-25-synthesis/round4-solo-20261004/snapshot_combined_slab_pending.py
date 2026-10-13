"""Freeze ALL unpaid rows of one accepted finite slab, not a search snapshot."""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from group_catalog import canonical, validate
from n25_outer_search import read, publish, bind, unchanged
from closed_origin_slab import rows

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--payments", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    args.payments, args.output = args.payments.resolve(), args.output.resolve()
    assert args.payments.is_relative_to(ROOT) and args.output.is_relative_to(ROOT)
    assert not args.output.exists()
    report_path = args.payments / "VERIFIED.json"
    report = read(report_path)
    assert report["verified"] and report["schema"] == "independent-finite-origin-slab-combined-payments-v1"
    assert report["source_sha256"] == sha(ROOT / "audit_finite_slab_filling_supplement.py")
    assert report["finite_rows_fully_scanned"] == 100000
    assert report["all_source_rows_partitioned_once_and_overlap_removed"]
    assert report["all_sparse_injections_and_complete_filling_trees_fresh_replayed"]
    assert report["not_a_complete_competitor_family_or_union"]
    unchanged(report["files_relative_to_workspace"])
    N, B, slab_index = report["N"], report["B"], report["slab_index"]
    assert N == 25 and B in (15, 16, 17)
    partition_path, pending_path = args.payments / "PARTITION.jsonl", args.payments / "PENDING.jsonl"
    assert sha(partition_path) == report["partition_sha256"]
    assert sha(pending_path) == report["pending_sha256"]
    matches = [relative for relative, digest in report["files_relative_to_workspace"].items()
               if digest == report["source_slab_sha256"] and relative.endswith(f".chunk-{slab_index}.jsonl")]
    assert len(matches) == 1
    source_slab = ROOT.parents[2] / matches[0]
    assert sha(source_slab) == report["source_slab_sha256"]
    selected, positions, paid, count = [], [], 0, 0
    header = {"schema": "finite-origin-slab-sparse-and-filling-ledger-v1",
              "N": N, "B": B, "slab_index": slab_index,
              "not_a_complete_competitor_family_or_union": True}
    with partition_path.open(encoding="ascii") as partition, pending_path.open(encoding="ascii") as pending:
        assert json.loads(next(partition), object_pairs_hook=no_duplicate_keys) == header
        assert json.loads(next(pending), object_pairs_hook=no_duplicate_keys) == header
        for index, row in rows(source_slab, B, slab_index):
            entry = json.loads(next(partition), object_pairs_hook=no_duplicate_keys)
            assert entry["slab_row"] == index
            assert (entry["centers"], entry["faces"]) == (row["centers"], row["faces"])
            if entry["status"] == "pending":
                assert json.loads(next(pending), object_pairs_hook=no_duplicate_keys) == entry
                assert entry["no_match_is_not_an_exclusion"]
                code, mapping = canonical(row["centers"], B, row["faces"], 1)
                assert list(code) == row["faces"] and len(mapping["centers"]) == row["centers"]
                validate(row["centers"], B, code, mapping, row["faces"])
                selected.append(row)
                positions.append({"pending_position": len(selected)-1, "slab_row": index})
            else:
                assert entry["status"] in ("strict-sparse-injection", "strict-complete-filling-family")
                paid += 1
            count += 1
        assert not partition.read().strip() and not pending.read().strip()
    assert count == 100000 and paid == report["total_paid_rows"]
    assert len(selected) == report["pending_rows"] > 0
    files = dict(report["files_relative_to_workspace"])
    for path in (Path(__file__), report_path, partition_path, pending_path, source_slab,
                 ROOT / "closed_origin_slab.py", HIGH / "group_catalog.py"):
        bind(files, path)
    unchanged(files)
    publish(args.output, {
        "schema": "incomplete-collar-discovery-v1", "N": N, "B": B,
        "weak_graph_count": len(selected), "weak_graphs": selected,
        "complete_necessary_outer_search": False, "global_optimality_proved": False,
        "scope": "ALL remaining unpaid rows of one independently accepted finite origin slab",
        "all_parent_pending_rows_frozen_once": True,
        "selected_source_positions": positions, "source_slab_sha256": report["source_slab_sha256"],
        "source_verified_sha256": sha(report_path), "source_pending_sha256": sha(pending_path),
        "all_selected_source_rows_and_canonical_codes_checked": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "not_a_complete_competitor_family_or_union": True,
    })
    print("ALL finite combined-slab pending rows frozen:", len(selected),
          "; not a complete B family", flush=True)


if __name__ == "__main__":
    main()
