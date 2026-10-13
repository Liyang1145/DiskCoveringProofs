"""Finite prefix proof proposals/replay from an immutable closed origin slab.

No native search is started or changed. The source slab and finite selection
are explicitly not a complete competitor family or a source of completion rates.
"""
from pathlib import Path
import argparse
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from group_catalog import canonical, validate
from n25_outer_search import read, publish
from batch_streamed_collar import identity

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--search", type=Path, required=True)
    ap.add_argument("--slab", type=int, default=0)
    ap.add_argument("--count", type=int, default=64)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    search, output = args.search.resolve(), args.output.resolve()
    assert search.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    assert 0 <= args.slab <= 1000 and 1 <= args.count <= 1024
    inputs = read(search / "INPUT-BINDINGS.json")
    N, B = inputs["N"], inputs["B"]
    assert N == 25 and B in (15, 16, 17)
    target = search / f"N25-B{B}-complete-origin-sorted-chunks.json"
    path = target.with_name(target.name+f".chunk-{args.slab}.jsonl")
    before = sha(path)
    selected, count, previous = [], 0, None
    with path.open(encoding="ascii") as stream:
        header = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
        assert header == {"schema": "sorted-outer-collar-slab-v1", "N": 25, "B": B,
                          "index": args.slab, "rows": 100000, "not_a_complete_search": True}
        for index, line in enumerate(stream):
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            centers, faces = row["centers"], row["faces"]
            assert B <= centers < N and faces == sorted(set(faces))
            assert all(type(m) is int and 0 < m < 1 << centers and m.bit_count() == 3
                       and m & ((1 << B)-1) for m in faces)
            used = 0
            for mask in faces:
                used |= mask
            assert used == (1 << centers)-1
            code = tuple(faces)
            assert previous is None or previous < code
            previous = code
            if index < args.count:
                canonical_code, mapping = canonical(centers, B, faces, 1)
                assert canonical_code == code
                validate(centers, B, faces, mapping, faces)
                selected.append({"id": index, "centers": centers, "faces": faces, "members": 1})
            count += 1
    assert count == header["rows"] and len(selected) == args.count and sha(path) == before
    output.mkdir()
    bindingpath = output / "bindings.jsonl"
    with bindingpath.open("x", encoding="ascii") as stream:
        for row in selected:
            stream.write(json.dumps({"index": row["id"], "group": row["id"], "map": identity(row["centers"], B)},
                                    separators=(",", ":"))+"\n")
    groupspath = output / "GROUPS.json"
    publish(groupspath, {
        "N": 25, "B": B, "threshold": 1, "groups": selected, "group_count": len(selected),
        "selected_types": len(selected), "catalog_types": header["rows"],
        "catalog_sha256": before, "bindings_file": bindingpath.name, "bindings_sha256": sha(bindingpath),
        "verified_embeddings_during_generation": True, "full_selected_catalog_scanned": False,
        "finite_selection_from_closed_slab_not_whole_family": True,
        "source_slab_relative_to_workspace": path.relative_to(ROOT).as_posix(),
        "source_slab_index": args.slab, "source_slab_is_not_complete_search": True,
        "actual_N25_cover_origin_condition_is_required": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    for script, arguments, label in (
        (ROOT / "probe_collar_batches.py", ["--groups", groupspath, "--output", output / "PROPOSALS",
                                           "--limit", 1, "--route-weak-realizable"], "PROPOSE"),
        (HIGH / "replay_group_stage.py", ["--groups", groupspath,
                                          "--receipt", output / "PROPOSALS/SUMMARY.json",
                                          "--output", output / "EXACT-REPLAY.json"], "REPLAY"),
    ):
        result = subprocess.run([sys.executable, str(script), *map(str, arguments)],
                                capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        publish(output / (label+"-TERMINAL.json"), {
            "actual_exit_code": result.returncode, "source_sha256": sha(script),
            "stdout": result.stdout.decode(errors="replace"), "stderr": result.stderr.decode(errors="replace"),
        })
        assert result.returncode == 0, (script, result.stdout, result.stderr)
    receipt, replay = read(output / "PROPOSALS/SUMMARY.json"), read(output / "EXACT-REPLAY.json")
    assert replay["verified"] and replay["exact_groups_replayed"] == receipt["excluded_groups"]
    assert replay["pending_groups"] == receipt["pending_groups"]
    assert replay["exact_groups_replayed"]+replay["pending_groups"] == args.count
    assert sha(path) == before and sha(groupspath) == replay["groups_sha256"]
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "finite-closed-origin-slab-prefix-exact-payments-v1", "N": 25, "B": B,
        "selected_source_rows": args.count, "strictly_excluded": replay["exact_groups_replayed"],
        "pending_rows": replay["pending_groups"],
        "all_selected_canonical_codes_and_identity_maps_checked": True,
        "all_selected_strict_trees_independent_standard_library_replayed": True,
        "source_slab_sha256": before, "groups_sha256": sha(groupspath),
        "receipt_sha256": sha(output / "PROPOSALS/SUMMARY.json"),
        "exact_replay_sha256": sha(output / "EXACT-REPLAY.json"),
        "source_sha256": sha(Path(__file__)),
        "not_a_complete_competitor_family_or_union": True,
        "pending_numeric_diagnostics_never_exclusions_or_actual_covers": True,
        "global_optimality_proved": False,
    })
    print("Finite closed-slab prefix independently paid:", replay["exact_groups_replayed"], "strict;",
          replay["pending_groups"], "pending; not a complete family", flush=True)


if __name__ == "__main__":
    main()
