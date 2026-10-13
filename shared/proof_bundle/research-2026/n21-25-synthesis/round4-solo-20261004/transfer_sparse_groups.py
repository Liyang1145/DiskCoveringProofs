"""Accept explicit proper-subgraph payments for a fixed group dataset.

Native matching only proposes maps. Every successful center/anchor/face
injection is checked by the frozen Python validator. Unmatched graphs remain
unpaid; no absence result is used as a theorem.
"""
from pathlib import Path
from collections import Counter
import argparse
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from group_catalog import validate
from stream_catalog import sha, no_duplicate_keys
from run_sparse_collar import sparse_library_gate
from n25_outer_search import publish, bind, unchanged
from test_outer_collar import linux_path, WSL

assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"),
                      object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    constants, library, table, files = sparse_library_gate(args.library.resolve())
    data = read(args.groups)
    assert (data["N"], data["B"], data["threshold"]) == (25, 14, 1)
    assert data["verified_embeddings_during_generation"]
    assert [g["id"] for g in data["groups"]] == list(range(data["group_count"]))
    assert data["group_count"] == len(data["groups"])
    for path in (args.groups, Path(__file__), HIGH / "group_catalog.py",
                 ROOT / "sparse_outer_match.cpp", ROOT / "sparse_outer_match-linux",
                 ROOT / "sparse_outer_matcher.inc"):
        bind(files, path)
    output.mkdir()
    requests, answers = output / "REQUESTS.tsv", output / "NATIVE-MAPS.json"
    with requests.open("x", encoding="ascii", newline="\n") as stream:
        for gid, group in enumerate(data["groups"]):
            centers, masks = group["centers"], group["faces"]
            assert 14 <= centers <= 25 and masks == sorted(set(masks)) and masks
            assert all(m > 0 and m < 1 << centers and m.bit_count() == 3
                       and m & ((1 << 14)-1) for m in masks)
            stream.write("\t".join(map(str, [gid, len(masks), *masks]))+"\n")
    relative = lambda path: os.path.relpath(path, ROOT).replace("\\", "/")
    assert all(relative(path).isascii() for path in (table, requests, answers))
    command = [WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C",
               linux_path(ROOT), "./sparse_outer_match-linux", "match", "25", "14",
               relative(table), relative(requests), relative(answers)]
    result = subprocess.run(command, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    publish(output / "NATIVE-TERMINAL.json", {
        "actual_exit_code": result.returncode, "command": command,
        "stdout": result.stdout.decode("utf8", errors="replace"),
        "stderr": result.stderr.decode("utf8", errors="replace"),
        "maps_are_only_proposals": True,
    })
    assert result.returncode == 0
    native = read(answers)
    assert native["scope"] == "sparse subgraph maps only"
    assert len(native["matches"]) == data["group_count"]
    byid = {o["id"]: o for o in library["obstacles"]}
    totals, unmatched, members = Counter(), [], 0
    with (output / "ACCEPTED-MAPS.jsonl").open("x", encoding="utf8") as ledger:
        for gid, match in enumerate(native["matches"]):
            assert match["request"] == gid
            group = data["groups"][gid]
            if match["obstacle"] == -1:
                unmatched.append(gid)
                continue
            assert match["obstacle"] in byid
            obstacle = byid[match["obstacle"]]
            mapping = {key: match[key] for key in ("centers", "anchors", "orientation", "shift")}
            validate(group["centers"], 14, obstacle["faces"], mapping, group["faces"])
            totals[obstacle["id"]] += 1
            members += group["members"]
            ledger.write(json.dumps({
                "group": gid, "obstacle": obstacle["id"], "map": mapping,
                "all_centers_anchors_and_image_faces_individually_checked": True,
            }, separators=(",", ":"))+"\n")
    unchanged(files)
    publish(output / "UNMATCHED-IDS.json", {
        "groups_sha256": sha(args.groups), "unmatched_group_ids": unmatched,
        "native_failure_to_match_not_used_as_a_noncontainment_proof": True,
    })
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "explicit-sparse-subgraph-group-payments-v1",
        "N": 25, "B": 14, "groups_sha256": sha(args.groups),
        "library_sha256": sha(args.library), "accepted_maps_sha256": sha(output / "ACCEPTED-MAPS.jsonl"),
        "unmatched_ids_sha256": sha(output / "UNMATCHED-IDS.json"),
        "native_maps_sha256": sha(answers), "matched_groups": sum(totals.values()),
        "unmatched_groups": len(unmatched), "associated_members_paid": members,
        "counts_by_obstacle": dict(totals),
        "all_successful_maps_explicitly_validated": True,
        "all_source_trees_fresh_exact_replayed": True,
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "complete_family_coverage_not_proved_here": True,
        "whole_catalog_exclusion_proved": False, "global_optimality_proved": False,
    })
    print("Explicit sparse transfers accepted:", sum(totals.values()), "groups;",
          len(unmatched), "unpaid; no family closure claim", flush=True)


if __name__ == "__main__":
    main()
