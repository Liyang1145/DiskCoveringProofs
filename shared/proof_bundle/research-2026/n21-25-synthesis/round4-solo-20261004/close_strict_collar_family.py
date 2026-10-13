"""Audit one simple-hole completion family whose entire catalog is strict."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from group_catalog import canonical_full, validate
from cross_order_strict_transfer import validate_disk
from complete_simple_collar import simple_holes
from n25_outer_search import read, bind, unchanged, publish

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--catalog-root", type=Path, required=True)
    ap.add_argument("--receipt", type=Path, required=True)
    ap.add_argument("--replay", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    source = args.catalog_root.resolve()
    assert source.is_relative_to(ROOT)
    groupspath = source / "GROUPS.json"
    groups, summary, collar, receipt, replay = map(read, (
        groupspath, source / "SUMMARY.json", source / "INPUT-COLLAR.json",
        args.receipt, args.replay))
    N, B = groups["N"], groups["B"]
    assert N == 25 and B in (14, 15, 16, 17) and groups["threshold"] == 0
    assert groups["complete_only_for_this_one_simple_hole_collar"]
    assert groups["not_a_complete_boundary_family"]
    assert summary["complete_this_collar_completion_search"]
    assert summary["source_sha256"] == sha(ROOT / "complete_simple_collar.py")
    assert summary["groups_sha256"] == sha(groupspath)
    assert summary["input_collar_sha256"] == sha(source / "INPUT-COLLAR.json")
    assert summary["maps_sha256"] == sha(source / "COLLAR-TO-COMPLETION.jsonl")
    assert groups["source_sha256"] == sha(ROOT / "complete_simple_collar.py")
    assert collar["N"] == N and collar["B"] == B
    assert simple_holes(collar["centers"], B, collar["faces"]) == collar["holes"]
    assert collar["new_inner_centers"] == N-collar["centers"]
    controls_path = ROOT / "simple-collar-completion-controls-20261005-v1.json"
    controls = read(controls_path)
    assert controls["verified"] and controls["all_handled_fibers_exactly_equal_to_full_reference"]
    assert controls["completion_source_sha256"] == sha(ROOT / "complete_simple_collar.py")
    assert controls["source_sha256"] == sha(ROOT / "test_simple_collar_completion.py")
    assert len(controls["cases"]) == 8 and len(controls["negative_controls_rejected"]) == 3
    assert replay["verified"] and (replay["N"], replay["B"]) == (N, B)
    assert replay["groups_sha256"] == receipt["groups_sha256"] == sha(groupspath)
    assert replay["receipt_sha256"] == sha(args.receipt)
    assert replay["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    count = groups["group_count"]
    assert count == len(groups["groups"]) == summary["full_graph_count"]
    assert [row["id"] for row in groups["groups"]] == list(range(count))
    assert count == replay["exact_groups_replayed"] == receipt["excluded_groups"]
    assert replay["pending_groups"] == receipt["pending_groups"] == 0
    assert F(replay["minimum_force_margin"]) > 0
    outcomes = {row["group"]: row for row in receipt["outcomes"]}
    assert len(outcomes) == len(receipt["outcomes"]) == count
    assert set(outcomes) == set(range(count))
    assert all(row["status"] == "excluded" for row in outcomes.values())
    assert replay["bindings_sha256"] == groups["bindings_sha256"] == sha(source / "bindings.jsonl")
    files = {}
    for path in (
        Path(__file__), ROOT / "complete_simple_collar.py", ROOT / "test_simple_collar_completion.py",
        ROOT / "SIMPLE-COLLAR-COMPLETION-SOURCE.md", controls_path,
        groupspath, source / "SUMMARY.json", source / "INPUT-COLLAR.json",
        source / "COLLAR-TO-COMPLETION.jsonl", source / "bindings.jsonl",
        args.receipt, args.replay, HIGH / "replay_group_stage.py", HIGH / "exact_graph.py",
        HIGH / "group_catalog.py", HIGH / "cross_order_strict_transfer.py",
        HIGH.parent / "round2-grouped/partial_force_exact.py",
        HIGH.parent / "evidence/core-reduction/constants/n25.json",
    ):
        bind(files, path)
    codes, mapped = set(), 0
    with (source / "COLLAR-TO-COMPLETION.jsonl").open(encoding="utf8") as stream:
        for gid, line in enumerate(stream):
            transfer = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert transfer["group"] == gid and gid < count
            group = groups["groups"][gid]
            code = tuple(group["faces"])
            assert group["centers"] == N and code not in codes
            codes.add(code)
            validate_disk(N, B, group["faces"])
            assert canonical_full(N, B, group["faces"]) == code
            validate(N, B, collar["faces"], transfer["map"], group["faces"])
            images = {sum(1 << transfer["map"]["centers"][v]
                          for v in range(collar["centers"]) if face >> v & 1)
                      for face in collar["faces"]}
            outer = {face for face in group["faces"] if face & ((1 << B)-1)}
            assert images == outer, "the source collar must be the complete outer face set"
            treepath = args.receipt.parent / f"group-{gid:07}.json.gz"
            assert sha(treepath) == outcomes[gid]["tree_sha256"]
            bind(files, treepath)
            mapped += 1
            if mapped % 2000 == 0:
                print("Strict fixed-collar full disk/map audit:", mapped, "/", count, flush=True)
    assert mapped == count == len(codes)
    unchanged(files)
    constants = read(HIGH.parent / "evidence/core-reduction/constants/n25.json")
    U = F(constants["radius_upper"])
    # r*² = 1-2sqrt(2)/3. This rational comparison proves U>r*.
    alpha = F(3, 2)*(1-U*U)
    assert 0 < alpha and alpha*alpha < 2
    publish(args.output, {
        "verified": True, "schema": "single-collar-strict-full-completion-closure-v1",
        "N": N, "B": B, "collar_centers": collar["centers"], "collar_faces": collar["faces"],
        "holes": collar["holes"], "new_inner_centers": collar["new_inner_centers"],
        "complete_this_simple_hole_completion_family": True,
        "full_completion_types": count, "strictly_excluded": count,
        "known_attaining_core_lower_paid": 0, "pending_completions": 0,
        "radius_threshold": str(U),
        "every_full_disk_and_exact_outer_face_map_rechecked": True,
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "simple_hole_source_induction_sha256": sha(ROOT / "SIMPLE-COLLAR-COMPLETION-SOURCE.md"),
        "all_other_outer_collars_not_paid_here": True, "global_optimality_proved": False,
    })
    print("One strict collar completion family closed:", count, "full types; pending 0;", flush=True)


if __name__ == "__main__":
    main()
