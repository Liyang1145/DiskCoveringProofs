"""Propose sparse payments for one already closed slab, without changing a job."""
from pathlib import Path
from collections import Counter
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import validate
from family_sparse_gate import sparse_library_gate
from verify_sparse_maps_fast import batch_match
from n25_outer_search import read, publish, bind, unchanged
from closed_origin_slab import rows, ledger_header

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--search", type=Path, required=True)
    ap.add_argument("--slab", type=int, default=0)
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    args.search, args.library, args.output = (
        p.resolve() for p in (args.search, args.library, args.output))
    assert all(p.is_relative_to(ROOT) for p in (args.search, args.library, args.output))
    assert not args.output.exists() and 0 <= args.slab <= 1000000
    inputs_path = args.search / "INPUT-BINDINGS.json"
    inputs = read(inputs_path)
    B = inputs["B"]
    assert inputs["N"] == 25 and B in (15, 16, 17)
    command = inputs["command"]
    assert command[7:10] == ["./peel_origin_streamed_collar-linux", "25", str(B)]
    assert command[-2:] == ["100000", "1"]
    slab_path = args.search / f"N25-B{B}-complete-origin-sorted-chunks.json.chunk-{args.slab}.jsonl"
    source_hash = sha(slab_path)
    constants, library, table, files = sparse_library_gate(args.library)
    assert library["B"] == B
    for path in (inputs_path, slab_path, args.library, Path(__file__),
                 ROOT / "closed_origin_slab.py", ROOT / "verify_sparse_maps_fast.py",
                 ROOT / "sparse_outer_match-linux", ROOT / "sparse_outer_match.cpp",
                 ROOT / "sparse_outer_matcher.inc", HIGH / "group_catalog.py"):
        bind(files, path)
    requests = [row["faces"] for index, row in rows(slab_path, B, args.slab)]
    args.output.mkdir()
    answers = batch_match(table, requests, args.output, 25, B)
    assert len(answers) == len(requests) == 100000
    byid = {o["id"]: o for o in library["obstacles"]}
    ledger = args.output / "PARTITION.jsonl"
    pending = args.output / "PENDING.jsonl"
    totals = Counter()
    with ledger.open("x", encoding="ascii") as paid, pending.open("x", encoding="ascii") as residual:
        for stream in (paid, residual):
            stream.write(json.dumps(ledger_header(25, B, args.slab), separators=(",", ":"))+"\n")
        for index, row in rows(slab_path, B, args.slab):
            answer = answers[index]
            assert answer["request"] == index and row["faces"] == requests[index]
            entry = {"slab_row": index, **row}
            assert type(answer["obstacle"]) is int
            if answer["obstacle"] >= 0:
                obstacle = byid[answer["obstacle"]]
                mapping = {key: answer[key] for key in ("centers", "anchors", "orientation", "shift")}
                assert len(mapping["centers"]) == obstacle["centers"] and len(mapping["anchors"]) == B
                validate(row["centers"], B, obstacle["faces"], mapping, row["faces"])
                entry.update(status="strict-sparse-injection", obstacle=obstacle["id"], map=mapping)
            else:
                assert answer["obstacle"] == -1
                entry.update(status="pending", no_match_is_not_an_exclusion=True)
                residual.write(json.dumps(entry, separators=(",", ":"))+"\n")
            totals[entry["status"]] += 1
            paid.write(json.dumps(entry, separators=(",", ":"))+"\n")
    assert sum(totals.values()) == 100000 and sha(slab_path) == source_hash
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    unchanged(files)
    publish(args.output / "PROPOSAL.json", {
        "schema": "finite-closed-origin-slab-sparse-partition-proposal-v1",
        "N": 25, "B": B, "slab_index": args.slab,
        "source_slab_relative_to_round4": slab_path.relative_to(ROOT).as_posix(),
        "source_slab_sha256": source_hash, "finite_rows": 100000,
        "strictly_paid_rows": totals["strict-sparse-injection"], "pending_rows": totals["pending"],
        "library_relative_to_round4": args.library.relative_to(ROOT).as_posix(),
        "library_sha256": sha(args.library), "partition_sha256": sha(ledger),
        "pending_sha256": sha(pending), "native_maps_sha256": sha(args.output / "NATIVE-MAPS.json"),
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "maps_all_explicitly_checked_during_proposal": True,
        "row_numbers_are_local_to_this_hash_bound_slab_not_final_union_ids": True,
        "not_a_complete_competitor_family_or_union": True,
        "global_optimality_proved": False,
    })
    print("Closed-slab sparse proposal:", totals["strict-sparse-injection"],
          "strict;", totals["pending"], "pending; finite slab only", flush=True)


if __name__ == "__main__":
    main()
