"""Exact coverage of noncontiguous original positions; no mathematical payment."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from library_parent_pending_worklist import consecutive_jobs

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    positions = [0, 1, 4, 5, 6, 8]
    jobs = consecutive_jobs(positions, 2)
    assert [(job["first"], job["count"], job["selected_offset"]) for job in jobs] == [
        (0, 2, 0), (4, 2, 2), (6, 1, 4), (8, 1, 5)]
    assert [i for job in jobs for i in range(job["first"], job["first"]+job["count"])] == positions
    rejected = []
    for label, selected, size in (
        ("duplicate-position", [0, 1, 1, 4], 2), ("unordered-position", [1, 0, 4], 2),
        ("negative-position", [-1, 0, 4], 2), ("boolean-position", [False, 1, 4], 2),
        ("empty-selection", [], 2), ("zero-batch", positions, 0),
        ("oversized-batch", positions, 1025), ("boolean-batch", positions, True),
    ):
        try:
            consecutive_jobs(selected, size)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("invalid original gapped positions accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "original-snapshot-gapped-job-partition-controls-v1",
        "all_selected_original_positions_covered_once_no_paid_gaps_included": True,
        "negative_controls_rejected": rejected, "source_sha256": sha(Path(__file__)),
        "selection_source_sha256": sha(ROOT / "library_parent_pending_worklist.py"),
        "functional_positions_not_family_exclusions": True, "global_optimality_proved": False,
    })
    print("Original-snapshot gapped jobs controls PASS:", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
