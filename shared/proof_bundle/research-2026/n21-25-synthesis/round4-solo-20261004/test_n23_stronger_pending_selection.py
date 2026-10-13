"""Functional previous-stage selection and attainment retention controls."""
from pathlib import Path
from copy import deepcopy
import argparse
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from refine_n23_pending_group_stage import remaining_ids

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    outcomes = [{"group": 0, "status": "excluded"}, {"group": 1, "status": "pending"},
                {"group": 2, "status": "pending"}]
    assert remaining_ids(outcomes, [0, 1, 2], 2) == [1, 2]
    rejected = []
    cases = [
        ("duplicate-selected-group", outcomes, [0, 1, 1, 2], 2),
        ("unordered-selected-group", outcomes, [2, 1, 0], 2),
        ("bool-selected-group", outcomes, [False, 1, 2], 2),
        ("out-of-range-group", outcomes, [0, 1, 2, 3], 2),
        ("known-group-not-selected", outcomes, [0, 1], 2),
        ("bool-known-group", outcomes, [0, 1, 2], True),
    ]
    changed = deepcopy(outcomes)
    changed[2]["status"] = "excluded"
    cases.append(("known-attainer-falsely-paid", changed, [0, 1, 2], 2))
    changed = deepcopy(outcomes)
    changed[1]["group"] = 2
    cases.append(("original-outcome-id-gap", changed, [0, 1, 2], 2))
    changed = deepcopy(outcomes)
    changed[1]["status"] = "success"
    cases.append(("unrecognized-outcome-status", changed, [0, 1, 2], 2))
    for label, rows, selected, known in cases:
        try:
            remaining_ids(rows, selected, known)
        except (AssertionError, IndexError, TypeError):
            rejected.append(label)
        else:
            raise AssertionError(("bad stronger stage selection accepted", label))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-stronger-pending-group-selection-controls-v1",
        "previous_positive_groups_not_selected": True, "known_attaining_group_retained": True,
        "negative_controls_rejected": rejected, "source_sha256": sha(Path(__file__)),
        "proposal_source_sha256": sha(ROOT / "refine_n23_pending_group_stage.py"),
        "functional_fixtures_not_full_types_or_payments": True, "global_optimality_proved": False,
    })
    print("N23 stronger pending selection controls PASS:", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
