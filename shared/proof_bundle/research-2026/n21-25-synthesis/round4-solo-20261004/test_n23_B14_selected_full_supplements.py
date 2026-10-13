"""Finite current-index selection refusals plus frozen full-type math controls."""
from pathlib import Path
from copy import deepcopy
from io import StringIO
import argparse
import json

from audit_n23_B14_selected_full_supplements import ROOT, select_actual_proposal_pending, read, sha, publish

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    indices = [1, 5, 12]
    rows = [{"index": 1, "status": "strict"}, {"index": 5, "status": "pending"},
            {"index": 12, "status": "strict"}]

    def invoke(pending=indices, outcomes=rows, count=3, counts={"strict": 2, "pending": 1}):
        return select_actual_proposal_pending(
            iter(pending), StringIO("".join(json.dumps(row)+"\n" for row in outcomes)), count, counts)

    assert invoke() == [5]
    cases = [
        ("missing-source-outcome", {"outcomes": rows[:-1]}),
        ("duplicate-source-outcome", {"outcomes": rows[:1]+rows}),
        ("extra-source-outcome", {"outcomes": rows+rows[-1:]}),
        ("wrong-actual-parent-index", {"pending": [1, 6, 12]}),
        ("wrong-full-source-count", {"count": 4}),
        ("wrong-previous-status-counts", {"counts": {"strict": 1, "pending": 2}}),
    ]
    changed = deepcopy(rows)
    changed[1]["status"] = "exact-candidate-full-type-retained"
    cases.append(("B15-candidate-status-not-a-B14-supplement", {"outcomes": changed}))
    changed = deepcopy(rows)
    changed[1]["index"] = True
    cases.append(("boolean-source-index", {"outcomes": changed}))
    rejected = []
    for label, kwargs in cases:
        try:
            invoke(**kwargs)
        except (AssertionError, ValueError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError(("invalid genuine complete-type supplement selection accepted", label))
    mathpath = ROOT / "n23-B14-full-type-controls-v1/VERIFIED.json"
    mathcontrols = read(mathpath)
    assert mathcontrols["verified"]
    assert mathcontrols["schema"] == "N23-B14-actual-full-residual-type-controls-v1"
    assert mathcontrols["audit_source_sha256"] == sha(ROOT / "audit_n23_B14_full_residual.py")
    assert mathcontrols["source_sha256"] == sha(ROOT / "test_n23_B14_full_residual.py")
    assert mathcontrols["positive_full_type_tree_mathematically_verified"]
    assert len(mathcontrols["negative_controls_rejected"]) == 15
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-B14-proposal-pending-full-supplement-selection-controls-v1",
        "negative_controls_rejected": rejected, "old_full_type_math_controls_sha256": sha(mathpath),
        "whole_type_math_checker_sha256": sha(ROOT / "audit_n23_B14_full_residual.py"),
        "audit_source_sha256": sha(ROOT / "audit_n23_B14_selected_full_supplements.py"),
        "proposal_source_sha256": sha(ROOT / "propose_n23_B14_selected_full_supplements.py"),
        "source_sha256": sha(Path(__file__)),
        "functional_fixture_identifiers_not_math_or_formal_parent_payments": True,
        "global_optimality_proved": False,
    })
    print("N23/B14 full supplement selection controls passed:", len(rejected), flush=True)


if __name__ == "__main__":
    main()
