"""Finite refusal controls for complete-type successor/old-payment selection."""
from copy import deepcopy
from pathlib import Path
import argparse

from audit_n23_complete_type_followup import ROOT, sha, publish, validate_row, read

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    row = {"index": 17, "outer_group": 369033}
    before = {"index": 17, "outer_group": 369033, "status": "pending"}
    after = {**before, "status": "strict", "tree_sha256": "fixture-tree-identity",
             "exact_result": {"fixture": "not a geometric force proof"}}
    validate_row(row, before, after, True)
    strict = deepcopy(after)
    validate_row(row, strict, {**strict, "certificate_path_relative_to_receipt": "bound-old-tree"}, False)
    core = {**before, "status": "exact-candidate-full-type-retained",
            "candidate_full_to_actual_map": {"fixture": "not a real full map"}}
    validate_row(row, core, deepcopy(core), False)
    cases = []
    for label, field, value in (
        ("wrong-source-index", "index", 18),
        ("wrong-original-group", "outer_group", 436330),
        ("known-core-not-new-strict-pending", "status", "exact-candidate-full-type-retained"),
    ):
        changed = deepcopy(after)
        changed[field] = value
        cases.append((label, (row, before, changed, True)))
    cases.append(("old-positive-not-new-pending", (row, strict, after, True)))
    changed = deepcopy(strict)
    changed["status"] = "pending"
    cases.append(("old-positive-payment-reopened", (row, strict, changed, False)))
    changed = deepcopy(strict)
    changed["tree_sha256"] = "altered"
    cases.append(("old-positive-proof-changed", (row, strict, changed, False)))
    changed = deepcopy(strict)
    changed["exact_result"] = {"altered": True}
    cases.append(("old-positive-math-result-changed", (row, strict, changed, False)))
    cases.append(("attaining-core-recast-as-strict", (row, core, after, False)))
    changed = deepcopy(core)
    changed["candidate_full_to_actual_map"] = {"altered": True}
    cases.append(("attaining-full-map-changed", (row, core, changed, False)))
    cases.append(("previous-pending-pretended-already-paid", (row, before, after, False)))
    rejected = []
    for label, values in cases:
        try:
            validate_row(*values)
        except (AssertionError, ValueError, KeyError):
            rejected.append(label)
        else:
            raise AssertionError(("invalid actual successor selection accepted", label))
    # The unchanged strict full-tree helper also has its existing sixteen
    # real identity/math refusal controls; do not manufacture a new identity.
    treecontrolpath = ROOT / "n23-B15-actual-full-type-tree-controls-solo-v1/VERIFIED.json"
    treecontrols = read(treecontrolpath)
    assert treecontrols["verified"]
    assert treecontrols["audit_source_sha256"] == sha(ROOT / "audit_n23_actual_full_type_stage.py")
    assert len(treecontrols["negative_controls_rejected"]) == 16
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-complete-type-followup-selection-controls-v1",
        "negative_controls_rejected": rejected,
        "unchanged_actual_full_tree_controls_sha256": sha(treecontrolpath),
        "frozen_full_tree_identity_checker_sha256": sha(ROOT / "audit_n23_actual_full_type_stage.py"),
        "audit_source_sha256": sha(ROOT / "audit_n23_complete_type_followup.py"),
        "source_sha256": sha(Path(__file__)),
        "selection_fixtures_not_mathematical_proof_payments": True,
        "global_optimality_proved": False,
    })
    print("N23 complete-type strict followup controls passed:", len(rejected), flush=True)


if __name__ == "__main__":
    main()
