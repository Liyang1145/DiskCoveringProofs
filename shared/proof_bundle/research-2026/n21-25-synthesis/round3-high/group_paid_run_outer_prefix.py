"""Group outer faces of an already-closed run for reusable force proposals.

Run rows are not final unique catalogue indices. This never pays completion
or final type coverage; subsequent force replays only prove weak graph facts.
"""
from pathlib import Path
from collections import Counter
import argparse
import json
import time
from paid_binary_residual import BinaryRows
from group_catalog import canonical
from audit_streamed_hierarchy import check_map
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", type=Path, required=True)
    ap.add_argument("--max-rows", type=int, default=100000)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    # Refuse a run still being written before creating any grouping outputs.
    run = BinaryRows(args.run, run=True)
    N, B = run.header["N"], run.header["B"]
    assert N in (23, 24, 25) and args.max_rows > 0
    expected_size = 28+4*(run.F+1)*run.header["orbits"]
    assert args.run.stat().st_size == expected_size, "run not closed/complete yet"
    before = sha(args.run)
    args.output.mkdir(parents=True)
    bindingpath = args.output / "bindings.jsonl"
    counts = Counter()
    codes = {}
    selected = 0
    started = time.monotonic()
    with bindingpath.open("x", encoding="utf8") as bindings:
        for index, row in run.rows():
            code, mapping = canonical(N, B, row["faces"], 1)
            gid = codes.setdefault(code, len(codes))
            centers = max(v for mask in code for v in range(N) if mask >> v & 1)+1
            check_map(N, B, {"centers": centers, "faces": list(code)}, mapping, set(row["faces"]), 1)
            counts[gid] += 1
            bindings.write(json.dumps({"index": index, "group": gid, "map": mapping},
                                      separators=(",", ":"))+"\n")
            selected += 1
            if selected % 10000 == 0:
                print("Closed-run prefix grouped", selected, "rows into", len(codes),
                      "weak graphs; seconds", round(time.monotonic()-started, 1), flush=True)
            if selected == args.max_rows and selected < run.header["orbits"]:
                run.stream.close()
                break
    assert sha(args.run) == before, "native run changed during prefix grouping"
    groups = [None]*len(codes)
    for code, gid in codes.items():
        groups[gid] = {"id": gid, "faces": list(code),
                       "centers": max(v for mask in code for v in range(N) if mask >> v & 1)+1,
                       "members": counts[gid]}
    result = {"N": N, "B": B, "threshold": 1, "groups": groups, "group_count": len(groups),
              "selected_types": selected, "catalog_types": run.header["orbits"],
              "catalog_sha256": before, "bindings_file": bindingpath.name,
              "bindings_sha256": sha(bindingpath),
              "verified_embeddings_during_generation": True,
              "full_selected_catalog_scanned": False,
              "parent_groups_sha256": None, "parent_proof_sha256": None,
              "source_sha256": sha(Path(__file__)),
              "canonicalizer_sha256": sha(ROOT / "group_catalog.py"),
              "mapping_acceptor_sha256": sha(ROOT / "audit_streamed_hierarchy.py"),
              "run_reader_sha256": sha(ROOT / "paid_binary_residual.py"),
              "rows_are_provisional_run_indices_not_final_unique_catalogue_indices": True,
              "not_a_complete_family": True, "global_optimality_proved": False,
              "scope": "weak-graph proposal inventory from one closed native-run prefix only"}
    (args.output / "GROUPS.json").write_text(json.dumps(result, indent=2), encoding="utf8")
    print("Closed-run proposal groups PASS:", selected, "run rows;", len(groups),
          "graphs; final catalogue coverage unpaid", flush=True)


if __name__ == "__main__":
    main()
