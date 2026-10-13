"""Exact dominance check: a new theorem is not necessarily a new guard."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import validate
from n25_outer_search import read, publish, bind, unchanged
from family_sparse_gate import sparse_library_gate
from verify_sparse_maps_fast import batch_match

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for key in ("snapshot", "receipt", "replay", "library", "output"):
        ap.add_argument("--"+key, type=Path, required=True)
    args = ap.parse_args()
    for key in vars(args):
        path = getattr(args, key).resolve()
        assert path.is_relative_to(ROOT)
        setattr(args, key, path)
    assert not args.output.exists()
    snapshot, receipt, replay = map(read, (args.snapshot, args.receipt, args.replay))
    assert snapshot["schema"] == "incomplete-collar-discovery-v1"
    assert receipt["snapshot_sha256"] == replay["snapshot_sha256"] == sha(args.snapshot)
    assert replay["verified"] and replay["receipt_sha256"] == sha(args.receipt)
    assert replay["source_sha256"] == sha(ROOT / "replay_family_discovery.py")
    assert replay["no_optimizer_imported"]
    assert replay["totals"]["excluded"] == len(snapshot["weak_graphs"])
    assert not replay["totals"].get("pending", 0)
    constants, library, table, files = sparse_library_gate(args.library)
    B = snapshot["B"]
    assert snapshot["N"] == 25 and library["B"] == B
    args.output.mkdir()
    requests = [row["faces"] for row in snapshot["weak_graphs"]]
    answers = batch_match(table, requests, args.output, 25, B)
    by_id = {row["id"]: row for row in library["obstacles"]}
    dominated, unmatched = [], []
    for index, (graph, answer) in enumerate(zip(snapshot["weak_graphs"], answers, strict=True)):
        assert answer["request"] == index
        if answer["obstacle"] >= 0:
            obstacle = by_id[answer["obstacle"]]
            mapping = {key: answer[key] for key in ("centers", "anchors", "orientation", "shift")}
            assert len(mapping["centers"]) == obstacle["centers"]
            validate(graph["centers"], B, obstacle["faces"], mapping, graph["faces"])
            dominated.append(index)
        else:
            assert answer["obstacle"] == -1
            unmatched.append(index)
    for path in (Path(__file__), args.snapshot, args.receipt, args.replay, args.library,
                 ROOT / "verify_sparse_maps_fast.py", ROOT / "sparse_outer_match-linux",
                 ROOT / "sparse_outer_match.cpp", ROOT / "sparse_outer_matcher.inc", HIGH / "group_catalog.py"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(args.output / "VERIFIED.json", {
        "verified": True, "schema": "existing-strict-library-dominance-of-new-force-candidates-v1",
        "N": 25, "B": B, "independently_strict_new_candidate_graphs": len(requests),
        "already_covered_by_existing_library": len(dominated),
        "not_matched_by_existing_library": len(unmatched),
        "dominated_candidate_indices": dominated, "unmatched_candidate_indices": unmatched,
        "all_positive_injections_checked_against_fresh_exact_source_theorems": True,
        "lack_of_existing_match_not_a_complete_family_claim": True,
        "library_sha256": sha(args.library), "source_sha256": sha(Path(__file__)),
        "files_relative_to_workspace": files, "global_optimality_proved": False,
    })
    print("Existing library dominance checked: B", B, len(dominated), "already paid;",
          len(unmatched), "unmatched new force graphs", flush=True)


if __name__ == "__main__":
    main()
