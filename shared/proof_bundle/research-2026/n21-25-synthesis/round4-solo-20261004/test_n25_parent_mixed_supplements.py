"""Real attaining source equality and disjoint strict/nonstrict route controls."""
from pathlib import Path
from copy import deepcopy
import argparse

from audit_n25_parent_mixed_supplements import (
    ROOT, eligible_parent, check_transport, read, publish, sha)

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    snapshotpath = ROOT / "n25-B16-all37624-complete-parent-pending-snapshot-20261005-v1.json"
    candidatepath = ROOT / "n25-B16-single-candidate-collar-closure-20261005-v1.json"
    transportpath = ROOT / "n25-B16-p115569-nonstrict1/VERIFIED.json"
    snapshot, candidate, transport = map(read, (snapshotpath, candidatepath, transportpath))
    original = next(row for row in snapshot["graphs"] if row["parent_index"] == 115569)
    actual = {"id": 115569, "centers": original["centers"], "faces": original["faces"]}
    check_transport(actual, original, transport, candidate, sha(snapshotpath))
    strict, nonstrict = {47808}, {115569}
    assert eligible_parent(47808, False, strict, nonstrict) == "strict"
    assert eligible_parent(115569, False, strict, nonstrict) == "nonstrict"
    assert eligible_parent(1, True, strict, nonstrict) == "unchanged"
    assert eligible_parent(2, False, strict, nonstrict) == "pending"
    rejected = []
    for label, pid, paid, strictids, nonstrictids in (
        ("strict-target-already-paid", 47808, True, strict, nonstrict),
        ("nonstrict-target-already-paid", 115569, True, strict, nonstrict),
        ("strict-and-nonstrict-parent-overlap", 115569, False, {115569}, nonstrict),
        ("boolean-parent-index", True, False, strict, nonstrict),
    ):
        try:
            eligible_parent(pid, paid, strictids, nonstrictids)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("invalid mixed parent route accepted", label))
    for label, field, value in (
        ("wrong-transport-parent", "parent_index", 115568),
        ("wrong-original-snapshot", "source_snapshot_sha256", "f"*64),
        ("same-count-omitted-source-face", "faces", actual["faces"][:-1]+[7]),
        ("no-literal-whole-face-proof", "entire_parent_outer_faces_literally_equal_not_proper_subgraph_or_count_only", False),
        ("no-real-original-parent-proof", "actual_complete_parent_source_row_and_genuine_original_pending_snapshot_matched", False),
        ("unexhausted-completion-search", "all_simple_hole_completions_freshly_reenumerated_without_node_budget", False),
        ("nonstrict-recast-strict", "strict_completion_types", 91),
        ("nonstrict-core-missing", "nonstrict_same_root_core_completion_types", 0),
        ("nonstrict-still-pending", "pending_completions", 1),
        ("wrong-same-root-value", "core_lower_radius", "1/4"),
    ):
        changed = deepcopy(transport)
        changed[field] = value
        try:
            check_transport(actual, original, changed, candidate, sha(snapshotpath))
        except (AssertionError, ValueError, KeyError):
            rejected.append(label)
        else:
            raise AssertionError(("invalid nonstrict whole parent transport accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N25-whole-parent-mixed-payment-controls-v1",
        "real_actual_attaining_parent_checked": 115569,
        "strict_nonstrict_oldpaid_and_remaining_routes_disjoint": True,
        "negative_controls_rejected": rejected,
        "audit_source_sha256": sha(ROOT / "audit_n25_parent_mixed_supplements.py"),
        "strict_checker_sha256": sha(ROOT / "audit_n25_parent_direct_supplements.py"),
        "nonstrict_checker_sha256": sha(ROOT / "audit_n25_attaining_parent_transport.py"),
        "source_sha256": sha(Path(__file__)),
        "functional_controls_not_full_parent_math_payment": True,
        "global_optimality_proved": False,
    })
    print("N25 mixed strict/nonstrict full-parent adoption controls passed:", len(rejected), flush=True)


if __name__ == "__main__":
    main()
