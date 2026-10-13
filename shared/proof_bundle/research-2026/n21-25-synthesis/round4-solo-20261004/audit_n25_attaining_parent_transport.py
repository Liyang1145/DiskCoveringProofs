"""Literal whole-outer source transport of the accepted nonstrict 91-type theorem.

The original 90 strict/core-one mathematical theorem is reused unchanged.
The actual full parent row and all simple-hole completions are checked again.
This does not yet merge the theorem into an entire B16 payment partition.
"""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish, unchanged
from batch_origin_collar import parent_gate, catalog_rows
from complete_simple_collar import simple_holes, enumerate_completions
from audit_streamed_hierarchy import check_map

assert __debug__


def match_parent(actual, original, candidate, N, B):
    assert (N, B) == (candidate["N"], candidate["B"]) == (25, 16)
    assert candidate["verified"] and candidate["schema"] == "single-n25-candidate-collar-completion-closure-v1"
    assert candidate["complete_this_simple_hole_completion_family"]
    assert (candidate["full_completion_types"], candidate["strictly_excluded"],
            candidate["known_attaining_core_lower_paid"], candidate["pending_completions"]) == (91, 90, 1, 0)
    assert candidate["attaining_group"] == 90
    assert candidate["core_lower_radius"] == "1/(sqrt(6)+sqrt(3))"
    assert type(actual["id"]) is int and type(original["parent_index"]) is int
    assert actual["id"] == original["parent_index"]
    assert actual["centers"] == original["centers"] == candidate["collar_centers"] == 24
    assert actual["faces"] == original["faces"] == candidate["collar_faces"]
    assert actual["faces"] == sorted(set(actual["faces"]))
    assert len(actual["faces"]) == 24


def main():
    ap = argparse.ArgumentParser()
    for name in ("snapshot", "candidate", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--parent-index", type=int, required=True)
    args = ap.parse_args()
    snapshotpath, candidatepath, controlpath, output = (
        getattr(args, name).resolve() for name in ("snapshot", "candidate", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (snapshotpath, candidatepath, controlpath, output))
    assert not output.exists() and 0 <= args.parent_index < 120782
    snapshot, candidate, controls = map(read, (snapshotpath, candidatepath, controlpath))
    assert snapshot["schema"] == "all-pending-complete-origin-parent-exact-graph-snapshot-v1"
    assert snapshot["source_sha256"] == sha(ROOT / "snapshot_complete_origin_pending.py")
    assert snapshot["all_full_parent_pending_rows_frozen_once"]
    assert snapshot["every_pending_parent_row_compared_against_full_catalog"]
    assert (snapshot["N"], snapshot["B"], snapshot["parent_weak_graphs"]) == (25, 16, 120782)
    assert candidate["source_sha256"] == sha(ROOT / "close_candidate_collar.py")
    assert candidate["simple_hole_source_induction_sha256"] == sha(ROOT / "SIMPLE-COLLAR-COMPLETION-SOURCE.md")
    assert controls["verified"] and controls["schema"] == "N25-exact-whole-parent-nonstrict-transport-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n25_attaining_parent_transport.py")
    assert controls["audit_source_sha256"] == sha(Path(__file__))
    assert controls["real_same_shape_different_parent_rejected"]
    unchanged(candidate["files_relative_to_workspace"])
    frozen = dict(snapshot["frozen_files"])
    for relative, digest in candidate["files_relative_to_workspace"].items():
        path = (ROOT.parents[2] / relative).resolve()
        assert path.is_relative_to(ROOT.parents[2])
        assert str(path) not in frozen or frozen[str(path)] == digest
        frozen[str(path)] = digest
    for path, digest in frozen.items():
        assert sha(path) == digest
    originals = {row["parent_index"]: row for row in snapshot["graphs"]}
    assert len(originals) == len(snapshot["graphs"]) == snapshot["selected_pending_graphs"] == 37624
    assert args.parent_index in originals
    parent = {key: Path(value) for key, value in snapshot["parent_inputs"].items()}
    union, catalogpath, _ = parent_gate(parent["manifest"], parent["terminal"], parent["union"])
    assert (union["N"], union["B"], union["unique_necessary_weak_graphs"]) == (25, 16, 120782)
    actual = None
    for row in catalog_rows(catalogpath, 25, 16, 120782):
        if row["id"] == args.parent_index:
            assert actual is None
            match_parent(row, originals[args.parent_index], candidate, 25, 16)
            actual = row
    assert actual is not None
    holes = simple_holes(24, 16, actual["faces"])
    completed, mappings, calls = enumerate_completions(25, 16, 24, actual["faces"], holes, 0)
    originalgroupspath = ROOT / "n25-B16-candidate-simple-hole-completions-20261005-v1/GROUPS.json"
    originalgroups = read(originalgroupspath)
    assert (originalgroups["N"], originalgroups["B"], originalgroups["threshold"],
            originalgroups["group_count"]) == (25, 16, 0, 91)
    assert len(completed) == len(mappings) == 91
    originalcodes = {tuple(group["faces"]): group["id"] for group in originalgroups["groups"]}
    assert originalcodes == completed
    completionmaps = []
    for code, gid in completed.items():
        target = originalgroups["groups"][gid]
        assert target["id"] == gid and target["centers"] == 25
        mapping = mappings[code]
        group = {"centers": 24, "faces": actual["faces"]}
        check_map(25, 16, group, mapping, set(target["faces"]), 1)
        completionmaps.append({"group": gid, "actual_parent_to_complete_type_map": mapping})
    for path in (Path(__file__), snapshotpath, candidatepath, controlpath, catalogpath,
                 originalgroupspath, ROOT / "complete_simple_collar.py",
                 ROOT / "SIMPLE-COLLAR-COMPLETION-SOURCE.md", HIGH / "audit_streamed_hierarchy.py"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    output.mkdir()
    publish(output / "PARENT-TO-COMPLETIONS.json", {
        "parent_index": args.parent_index, "N": 25, "B": 16,
        "all91_actual_complete_face_center_and_anchor_maps": completionmaps,
        "source_sha256": sha(Path(__file__)), "not_an_entire_B16_payment_partition": True,
    })
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N25-literal-whole-parent-nonstrict-completion-theorem-transport-v1",
        "N": 25, "B": 16, "parent_index": args.parent_index,
        "complete_parent_weak_graphs": 120782, "centers": 24, "faces": actual["faces"],
        "actual_complete_parent_source_row_and_genuine_original_pending_snapshot_matched": True,
        "entire_parent_outer_faces_literally_equal_not_proper_subgraph_or_count_only": True,
        "all_simple_hole_completions_freshly_reenumerated_without_node_budget": True,
        "completion_search_calls": calls, "full_completion_types": 91,
        "strict_completion_types": 90, "nonstrict_same_root_core_completion_types": 1,
        "pending_completions": 0, "core_lower_radius": candidate["core_lower_radius"],
        "old90_strict_and311883_node_core_math_theorem_reused_unchanged_not_fresh_replay_claim": True,
        "not_a_strict_upper_radius_exclusion_of_the_attaining_parent": True,
        "not_yet_adopted_into_entire_complete_parent_payment_partition": True,
        "source_snapshot_sha256": sha(snapshotpath), "candidate_theorem_sha256": sha(candidatepath),
        "parent_to_completions_sha256": sha(output / "PARENT-TO-COMPLETIONS.json"),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "source_cover_transport_other_parents_families_and_global_assembly_still_owed": True,
        "global_optimality_proved": False,
    })
    print("N25 actual whole parent nonstrict completion theorem transported:", args.parent_index,
          "90 strict +1 same-root core; full-parent adoption still owed", flush=True)


if __name__ == "__main__":
    main()
