"""Close only the n25/B16 candidate outer collar's 91 completion types."""
from pathlib import Path
from fractions import Fraction as F
import json
import sys
import argparse

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
WORK = ROOT.parents[2].resolve()
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from group_catalog import validate
from replay_n25_tight_domain import inputs
from complete_simple_collar import full_code_map, simple_holes
from n25_outer_search import bind, unchanged

assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    catalog_root = ROOT / "n25-B16-candidate-simple-hole-completions-20261005-v1"
    groupspath = catalog_root / "GROUPS.json"
    catalog_summary = read(catalog_root / "SUMMARY.json")
    groups = read(groupspath)
    collar = read(catalog_root / "INPUT-COLLAR.json")
    controls_path = ROOT / "simple-collar-completion-controls-20261005-v1.json"
    controls = read(controls_path)
    assert controls["verified"] and controls["source_sha256"] == sha(ROOT / "test_simple_collar_completion.py")
    assert controls["completion_source_sha256"] == sha(ROOT / "complete_simple_collar.py")
    assert controls["all_handled_fibers_exactly_equal_to_full_reference"]
    assert len(controls["cases"]) == 8 and len(controls["negative_controls_rejected"]) == 3
    assert any(row["largest_missing_inner_budget"] > 0 for row in controls["cases"])
    assert catalog_summary["complete_this_collar_completion_search"]
    assert catalog_summary["source_sha256"] == sha(ROOT / "complete_simple_collar.py")
    assert catalog_summary["input_collar_sha256"] == sha(catalog_root / "INPUT-COLLAR.json")
    assert catalog_summary["groups_sha256"] == sha(groupspath)
    assert catalog_summary["maps_sha256"] == sha(catalog_root / "COLLAR-TO-COMPLETION.jsonl")
    assert (groups["N"], groups["B"], groups["group_count"]) == (25, 16, 91)
    assert collar["centers"] == 24 and collar["new_inner_centers"] == 1
    assert simple_holes(24, 16, collar["faces"]) == collar["holes"]
    receiptpath = ROOT / "n25-B16-candidate-completion-force-20261005-v1/SUMMARY.json"
    strictpath = ROOT / "n25-B16-candidate-90-completion-fresh-exact.json"
    receipt, strict = map(read, (receiptpath, strictpath))
    assert strict["verified"] and strict["groups_sha256"] == receipt["groups_sha256"] == sha(groupspath)
    assert strict["receipt_sha256"] == sha(receiptpath)
    assert strict["source_sha256"] == sha(HIGH / "replay_group_stage.py")
    assert strict["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert strict["exact_groups_replayed"] == receipt["excluded_groups"] == 90
    assert strict["pending_groups"] == receipt["pending_groups"] == 1
    outcomes = {row["group"]: row for row in receipt["outcomes"]}
    assert set(outcomes) == set(range(91))
    pending = [gid for gid, row in outcomes.items() if row["status"] == "pending"]
    assert pending == [receipt["known_attaining_group_control"]] == [90]
    core_replay_path = ROOT / "n25-tight-core-fresh-exact-replay.json"
    core_replay = read(core_replay_path)
    constants, masks, local, current_bound, core = inputs(-1)
    treepath = HIGH / "evidence/n25-endpoint-negative-angle-tight-pruned-resume1.json.gz"
    assert core_replay["verified"] and core_replay["entire_angle_domain_proved"]
    assert core_replay["pending_boxes"] == 0 and core_replay["nodes"] == 311883
    assert core_replay["source_sha256"] == sha(HIGH / "replay_n25_tight_domain.py")
    assert core_replay["input_sha256"] == current_bound
    assert core_replay["tree_sha256"] == sha(treepath)
    assert F(core_replay["minimum_force_margin"]) > 0
    assert F(core_replay["minimum_local_margin"]) > 0
    snapshot_path = HIGH / "evidence/N25-ENDPOINT-CORE-LOWER-SNAPSHOT-resume1.json"
    snapshot = read(snapshot_path)
    assert snapshot["verified"] and snapshot["file_count"] == len(snapshot["files"]) == 42
    for relative, digest in snapshot["files"].items():
        assert sha(WORK / relative) == digest
    geometrypath = HIGH / "evidence/n25-isolation-exact-resume1/rotated-geometry.json"
    geometry = read(geometrypath)
    full = sorted(sum(1 << v for v in face) for face in geometry["faces"])
    code, mapping = full_code_map(25, 16, full)
    target = groups["groups"][90]
    assert target["id"] == 90 and target["centers"] == 25 and tuple(target["faces"]) == code
    validate(25, 16, masks, mapping, target["faces"])
    assert masks == sorted(sum(1 << v for v in face) for face in core["faces"])
    with (catalog_root / "COLLAR-TO-COMPLETION.jsonl").open(encoding="utf8") as stream:
        maps = [json.loads(line, object_pairs_hook=no_duplicate_keys) for line in stream]
    assert [row["group"] for row in maps] == list(range(91))
    for row, target_group in zip(maps, groups["groups"], strict=True):
        validate(25, 16, collar["faces"], row["map"], target_group["faces"])
    files = {}
    for path in (
        Path(__file__), ROOT / "complete_simple_collar.py", ROOT / "test_simple_collar_completion.py",
        ROOT / "SIMPLE-COLLAR-COMPLETION-SOURCE.md", controls_path,
        groupspath, catalog_root / "SUMMARY.json", catalog_root / "INPUT-COLLAR.json",
        catalog_root / "COLLAR-TO-COMPLETION.jsonl", catalog_root / "bindings.jsonl",
        receiptpath, strictpath, core_replay_path, treepath, snapshot_path, geometrypath,
        HIGH / "replay_n25_tight_domain.py", HIGH / "replay_n25_endpoint_domain.py",
        HIGH / "replay_group_stage.py", HIGH / "exact_graph.py", HIGH / "group_catalog.py",
        HIGH.parent / "round2-grouped/partial_force_exact.py",
    ):
        bind(files, path)
    files.update(snapshot["files"])
    for gid, outcome in outcomes.items():
        if outcome["status"] == "excluded":
            path = receiptpath.parent / f"group-{gid:07}.json.gz"
            assert sha(path) == outcome["tree_sha256"]
            bind(files, path)
    unchanged(files)
    args.output.write_text(json.dumps({
        "verified": True, "schema": "single-n25-candidate-collar-completion-closure-v1",
        "N": 25, "B": 16, "collar_centers": 24, "collar_faces": collar["faces"],
        "complete_this_simple_hole_completion_family": True,
        "full_completion_types": 91, "strictly_excluded": 90,
        "known_attaining_core_lower_paid": 1, "pending_completions": 0,
        "attaining_group": 90, "negative_endpoint_core_to_attaining_full_graph": mapping,
        "core_lower_radius": "1/(sqrt(6)+sqrt(3))",
        "collar_continuous_realizability_not_mistaken_for_a_cover": True,
        "simple_hole_source_induction_sha256": sha(ROOT / "SIMPLE-COLLAR-COMPLETION-SOURCE.md"),
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "all_other_B16_collars_not_paid_here": True,
        "global_optimality_proved": False,
        "scope": "one candidate outer collar and all of its 91 simple-hole completions only",
    }, indent=2)+"\n", encoding="utf8")
    print("Single n25/B16 candidate collar completion closure PASS: 90 strict + 1 core; pending 0;",
          "not the complete B16 or n25 theorem", flush=True)


if __name__ == "__main__":
    main()
