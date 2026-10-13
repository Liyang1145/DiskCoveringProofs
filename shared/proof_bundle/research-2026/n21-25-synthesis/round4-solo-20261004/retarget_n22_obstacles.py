"""Freshly re-accept old strict forces on a new n25 family's entire angle root.

The target acceptance uses n25's own angle constraints and radius, not merely
a smaller-radius assertion or a reused historical verification flag.
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
WORK = ROOT.parents[2].resolve()
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys

assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"),
                      object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--B", type=int, choices=(14, 15), required=True)
    ap.add_argument("--count", type=int)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    library = read(args.library)
    assert library["verified"] and library["schema"] == "strict-obstacle-library-v1"
    assert not args.output.exists()
    oldpath = ROOT.parent / "evidence/core-reduction/constants/n22.json"
    newpath = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    old, new = map(read, (oldpath, newpath))
    assert old["verified"] and old["N"] == 22
    assert new["verified"] and new["N"] == 25
    assert F(new["radius_upper"]) < F(old["radius_upper"]) == F(library["radius_threshold"])
    source = [o for o in library["obstacles"] if o["B"] == args.B]
    if args.count is not None:
        assert args.count > 0
        source = source[:args.count]
    assert source
    output = args.output.resolve()
    assert output.is_relative_to(ROOT)
    output.mkdir()
    accepted, attempts, totals = [], [], Counter()
    started = time.monotonic()
    with (output / "attempts.jsonl").open("x", encoding="utf8") as ledger:
        for index, obstacle in enumerate(source):
            treepath = WORK / obstacle["tree_file_relative_to_workspace"]
            assert sha(treepath) == obstacle["tree_sha256"]
            with gzip.open(treepath, "rt", encoding="utf8") as stream:
                tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
            assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
                22, args.B, obstacle["centers"], obstacle["faces"])
            assert tree["constants_sha256"] == sha(oldpath)
            assert tree["radius_upper"] == old["radius_upper"]
            assert all(node["kind"] in ("EMPTY", "SPLIT", "DUAL") for node in tree["nodes"])
            original = exact.verify(args.B, obstacle["centers"], obstacle["faces"],
                                    tree["nodes"], old)
            assert original == obstacle["fresh_exact_replay"]
            try:
                target = exact.verify(args.B, obstacle["centers"], obstacle["faces"],
                                      tree["nodes"], new)
            except AssertionError:
                attempt = {"source_obstacle": obstacle["id"], "status": "pending",
                           "reason": "old force/tree not directly accepted on target root; no exclusion claimed"}
            else:
                assert F(target["minimum_force_margin"]) > 0
                gid = len(accepted)
                accepted.append((obstacle, tree["nodes"], target))
                attempt = {"source_obstacle": obstacle["id"], "status": "excluded",
                           "target_group": gid, "target_fresh_exact_replay": target,
                           "source_tree_sha256": sha(treepath)}
            totals[attempt["status"]] += 1
            attempts.append(attempt)
            ledger.write(json.dumps(attempt, separators=(",", ":"))+"\n")
            if (index+1) % 500 == 0:
                ledger.flush()
                print("N25/B", args.B, "retargeted", index+1, dict(totals),
                      "seconds", round(time.monotonic()-started, 2), flush=True)
    groups = [{"id": gid, "centers": o["centers"], "faces": o["faces"], "members": 1}
              for gid, (o, nodes, report) in enumerate(accepted)]
    bindings = output / "bindings.jsonl"
    with bindings.open("x", encoding="utf8") as stream:
        for group in groups:
            stream.write(json.dumps({
                "index": group["id"], "group": group["id"],
                "map": {"centers": list(range(group["centers"])),
                        "anchors": list(range(args.B)), "orientation": 1, "shift": 0},
            }, separators=(",", ":"))+"\n")
    group_path = output / "GROUPS.json"
    group_path.write_text(json.dumps({
        "N": 25, "B": args.B, "threshold": 1, "groups": groups, "group_count": len(groups),
        "selected_types": len(groups), "catalog_types": len(groups),
        "catalog_sha256": sha(output / "attempts.jsonl"), "bindings_file": bindings.name,
        "bindings_sha256": sha(bindings), "verified_embeddings_during_generation": True,
        "full_selected_catalog_scanned": False, "parent_groups_sha256": None,
        "parent_proof_sha256": None, "not_a_complete_family": True,
        "members_are_standalone_graphs_not_target_cover_types": True,
        "source_library_sha256": sha(args.library), "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    outcomes = []
    for group, (obstacle, nodes, report) in zip(groups, accepted, strict=True):
        treepath = output / f"group-{group['id']:07}.json.gz"
        with gzip.open(treepath, "xt", encoding="utf8") as stream:
            json.dump({
                "N": 25, "B": args.B, "partial_centers": group["centers"],
                "faces": group["faces"], "nodes": nodes, "groups_sha256": sha(group_path),
                "constants_sha256": sha(newpath), "radius_upper": new["radius_upper"],
            }, stream, separators=(",", ":"))
        outcomes.append({"group": group["id"], "status": "excluded", **report,
                         "members": 1, "tree_sha256": sha(treepath)})
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    (output / "SUMMARY.json").write_text(json.dumps({
        "N": 25, "B": args.B, "groups_sha256": sha(group_path), "outcomes": outcomes,
        "excluded_groups": len(groups), "pending_groups": 0,
        "catalog_members_excluded": len(groups), "requested_groups_complete": True,
        "source_obstacles_attempted": len(source), "source_obstacles_not_directly_retargeted": totals["pending"],
        "source_library_sha256": sha(args.library), "attempts_sha256": sha(output / "attempts.jsonl"),
        "target_constants_sha256": sha(newpath), "source_constants_sha256": sha(oldpath),
        "source_sha256": sha(Path(__file__)), "no_optimizer_imported": True,
        "whole_catalog_exclusion_proved": False, "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    print("N25/B", args.B, "fresh retarget acceptance:", dict(totals),
          "; standalone graph theorems, not a target family closure", flush=True)


if __name__ == "__main__":
    main()
