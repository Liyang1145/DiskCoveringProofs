"""Locate exact whole outer matches in the genuine original B16 root residual.

This establishes only a source graph identity and face/anchor maps. It does
not transport or adopt the historical nonstrict completion theorem.
"""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import canonical
from audit_streamed_hierarchy import check_map
from n25_outer_search import read, publish

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("snapshot", "candidate", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    snapshotpath, candidatepath, output = (
        getattr(args, name).resolve() for name in ("snapshot", "candidate", "output"))
    assert all(path.is_relative_to(ROOT) for path in (snapshotpath, candidatepath, output))
    assert not output.exists()
    snapshot, candidate = read(snapshotpath), read(candidatepath)
    assert snapshot["schema"] == "all-pending-complete-origin-parent-exact-graph-snapshot-v1"
    assert snapshot["source_sha256"] == sha(ROOT / "snapshot_complete_origin_pending.py")
    assert snapshot["all_full_parent_pending_rows_frozen_once"]
    assert snapshot["every_pending_parent_row_compared_against_full_catalog"]
    assert (snapshot["N"], snapshot["B"], snapshot["parent_weak_graphs"]) == (25, 16, 120782)
    assert len(snapshot["graphs"]) == snapshot["selected_pending_graphs"] == 37624
    assert candidate["verified"] and candidate["schema"] == "single-n25-candidate-collar-completion-closure-v1"
    assert (candidate["N"], candidate["B"]) == (25, 16)
    faces = candidate["collar_faces"]
    code, candidatemap = canonical(25, 16, faces, 1)
    group = {"centers": len(candidatemap["centers"]), "faces": list(code)}
    assert group["centers"] == candidate["collar_centers"] == 24
    assert len(code) == len(faces)
    check_map(25, 16, group, candidatemap, set(faces), 1)
    frozen = dict(snapshot["frozen_files"])
    for path, digest in frozen.items():
        assert sha(path) == digest
    for path in (Path(__file__), snapshotpath, candidatepath,
                 HIGH / "group_catalog.py", HIGH / "audit_streamed_hierarchy.py"):
        frozen[str(path)] = sha(path)
    matches, compared, parentids = [], 0, set()
    for position, row in enumerate(snapshot["graphs"]):
        pid = row["parent_index"]
        assert type(pid) is int and pid not in parentids
        parentids.add(pid)
        if row["centers"] != group["centers"] or len(row["faces"]) != len(code):
            continue
        actualcode, mapping = canonical(25, 16, row["faces"], 1)
        compared += 1
        if actualcode == code:
            check_map(25, 16, group, mapping, set(row["faces"]), 1)
            assert len(mapping["centers"]) == row["centers"]
            matches.append({
                "original_snapshot_position": position, "parent_index": pid,
                "centers": row["centers"], "faces": row["faces"],
                "candidate_to_common_code_map": candidatemap,
                "parent_to_common_code_map": mapping,
                "exact_whole_outer_code_equal_not_a_proper_subgraph_match": True,
            })
        if compared % 5000 == 0:
            print("N25/B16 actual whole outer candidate identity scan", compared,
                  "comparable source rows; matches", len(matches), flush=True)
    for path, digest in frozen.items():
        assert sha(path) == digest
    output.mkdir()
    publish(output / "FOUND.json", {
        "N": 25, "B": 16, "original_snapshot_graphs": 37624,
        "whole_shape_comparable_graphs": compared, "exact_matches": matches,
        "candidate_whole_outer_code": list(code), "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)),
        "identity_only_nonstrict_completion_theorem_transport_not_adopted": True,
        "global_optimality_proved": False,
    })
    print("N25/B16 exact candidate whole outer source matches:", len(matches),
          "; no theorem/payment transport here", flush=True)


if __name__ == "__main__":
    main()
