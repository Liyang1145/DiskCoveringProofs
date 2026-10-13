"""Reject same-size wrong actual parent and malformed nonstrict theorem identities."""
from pathlib import Path
from copy import deepcopy
import argparse

from audit_n25_attaining_parent_transport import ROOT, match_parent, read, sha, publish

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    snapshotpath = ROOT / "n25-B16-all37624-complete-parent-pending-snapshot-20261005-v1.json"
    candidatepath = ROOT / "n25-B16-single-candidate-collar-closure-20261005-v1.json"
    snapshot, candidate = read(snapshotpath), read(candidatepath)
    rows = {row["parent_index"]: row for row in snapshot["graphs"]}
    original = rows[115569]
    actual = {"id": 115569, "centers": original["centers"], "faces": original["faces"]}
    match_parent(actual, original, candidate, 25, 16)
    rejected = []
    wrong = rows[47808]
    assert wrong["centers"] == original["centers"] and len(wrong["faces"]) == len(original["faces"])
    assert wrong["faces"] != original["faces"]
    cases = [
        ("same-size-real47808-is-not-attaining-parent",
         {"id": 47808, "centers": wrong["centers"], "faces": wrong["faces"]}, wrong, candidate, 25, 16),
        ("wrong-N", actual, original, candidate, 24, 16),
        ("wrong-B", actual, original, candidate, 25, 17),
    ]
    for label, field, value in (
        ("wrong-source-parent-id", "id", 115570),
        ("wrong-parent-center-count", "centers", 23),
        ("omitted-parent-outer-face", "faces", actual["faces"][:-1]),
        ("duplicated-parent-outer-face", "faces", actual["faces"]+[actual["faces"][-1]]),
    ):
        changed = deepcopy(actual)
        changed[field] = value
        cases.append((label, changed, original, candidate, 25, 16))
    changed = deepcopy(original)
    changed["parent_index"] = 115570
    cases.append(("wrong-original-snapshot-index", actual, changed, candidate, 25, 16))
    for label, field, value in (
        ("incomplete-candidate-family", "complete_this_simple_hole_completion_family", False),
        ("wrong-completion-count", "full_completion_types", 90),
        ("attainer-miscast-as-strict", "strictly_excluded", 91),
        ("missing-nonstrict-core-payment", "known_attaining_core_lower_paid", 0),
        ("candidate-still-pending", "pending_completions", 1),
        ("wrong-exact-lower-radius", "core_lower_radius", "239146311738101/1000000000000000"),
    ):
        changed = deepcopy(candidate)
        changed[field] = value
        cases.append((label, actual, original, changed, 25, 16))
    for label, row, snap, theorem, N, B in cases:
        try:
            match_parent(row, snap, theorem, N, B)
        except (AssertionError, ValueError, KeyError):
            rejected.append(label)
        else:
            raise AssertionError(("bad whole-parent nonstrict transport identity accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N25-exact-whole-parent-nonstrict-transport-controls-v1",
        "actual_attaining_parent_positive_control": 115569,
        "real_same_shape_different_parent_rejected": True,
        "negative_controls_rejected": rejected,
        "snapshot_sha256": sha(snapshotpath), "candidate_theorem_sha256": sha(candidatepath),
        "audit_source_sha256": sha(ROOT / "audit_n25_attaining_parent_transport.py"),
        "source_sha256": sha(Path(__file__)),
        "functional_identity_controls_not_new_math_core_replays": True,
        "global_optimality_proved": False,
    })
    print("N25 actual whole-parent nonstrict transport identity controls passed:", len(rejected), flush=True)


if __name__ == "__main__":
    main()
