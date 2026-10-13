"""Finite discovery snapshot spread across unpaid positions of a closed slab.

This is a new, provenance-labelled input adapter for frozen discovery tools;
it does not imitate a completed enumeration or make a theorem from sampling.
"""
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
from closed_origin_slab import rows, ledger_header

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--payments", type=Path, required=True)
    ap.add_argument("--count", type=int, default=256)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    args.payments, args.output = args.payments.resolve(), args.output.resolve()
    assert args.payments.is_relative_to(ROOT) and args.output.is_relative_to(ROOT)
    assert not args.output.exists()
    verified_path, proposal_path = args.payments / "VERIFIED.json", args.payments / "PROPOSAL.json"
    verified, proposal = read(verified_path), read(proposal_path)
    assert verified["verified"] and verified["schema"] == "independent-finite-origin-slab-sparse-partition-v1"
    assert verified["source_sha256"] == sha(ROOT / "replay_closed_origin_slab.py")
    assert verified["proposal_sha256"] == sha(proposal_path)
    assert verified["not_a_complete_competitor_family_or_union"]
    N, B, slab_index = proposal["N"], proposal["B"], proposal["slab_index"]
    assert (verified["N"], verified["B"], verified["slab_index"]) == (N, B, slab_index)
    pending_path = args.payments / "PENDING.jsonl"
    assert sha(pending_path) == proposal["pending_sha256"] == verified["pending_sha256"]
    total = verified["pending_rows"]
    assert 2 <= args.count <= min(total, 1024)
    positions = {j*(total-1)//(args.count-1) for j in range(args.count)}
    assert len(positions) == args.count
    selected, original_indices, count, previous = [], [], 0, -1
    with pending_path.open(encoding="ascii") as stream:
        assert json.loads(next(stream), object_pairs_hook=no_duplicate_keys) == ledger_header(N, B, slab_index)
        for pending_index, line in enumerate(stream):
            entry = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert set(entry) == {"slab_row", "centers", "faces", "status", "no_match_is_not_an_exclusion"}
            assert entry["status"] == "pending" and entry["no_match_is_not_an_exclusion"]
            assert type(entry["slab_row"]) is int and previous < entry["slab_row"] < 100000
            previous = entry["slab_row"]
            if pending_index in positions:
                code, mapping = canonical(entry["centers"], B, entry["faces"], 1)
                assert list(code) == entry["faces"] and len(mapping["centers"]) == entry["centers"]
                validate(entry["centers"], B, code, mapping, entry["faces"])
                selected.append({"centers": entry["centers"], "faces": entry["faces"]})
                original_indices.append({"pending_position": pending_index, "slab_row": entry["slab_row"]})
            count += 1
    assert count == total and len(selected) == args.count
    source_slab = (ROOT / proposal["source_slab_relative_to_round4"]).resolve()
    assert source_slab.is_relative_to(ROOT)
    assert sha(source_slab) == proposal["source_slab_sha256"] == verified["source_slab_sha256"]
    chosen = {row["slab_row"]: graph for row, graph in zip(original_indices, selected, strict=True)}
    found = 0
    for index, row in rows(source_slab, B, slab_index):
        if index in chosen:
            assert row == chosen[index]
            found += 1
    assert found == args.count
    files = dict(verified["files_relative_to_workspace"])
    for path in (Path(__file__), verified_path, proposal_path, pending_path, source_slab,
                 ROOT / "closed_origin_slab.py", HIGH / "group_catalog.py"):
        bind(files, path)
    unchanged(files)
    publish(args.output, {
        "schema": "incomplete-collar-discovery-v1", "N": N, "B": B,
        "weak_graph_count": len(selected), "weak_graphs": selected,
        "complete_necessary_outer_search": False, "global_optimality_proved": False,
        "scope": "finite sample of unpaid positions in one immutable closed origin slab",
        "no_enumeration_or_exhaustion_performed_by_this_adapter": True,
        "selection_method": "floor(j*(pending_count-1)/(sample_count-1)), j=0..sample_count-1",
        "selected_source_positions": original_indices,
        "source_slab_sha256": sha(source_slab), "source_pending_count": total,
        "source_pending_sha256": sha(pending_path), "source_verified_sha256": sha(verified_path),
        "all_selected_source_rows_and_canonical_codes_checked": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "numeric_or_unmatched_samples_not_actual_counterexamples": True,
        "not_a_complete_competitor_family_or_union": True,
    })
    print("Finite pending-slab discovery snapshot:", len(selected), "graphs from",
          total, "unpaid rows; not a complete family", flush=True)


if __name__ == "__main__":
    main()
