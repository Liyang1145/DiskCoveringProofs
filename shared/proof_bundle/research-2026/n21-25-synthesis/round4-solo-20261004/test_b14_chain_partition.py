"""Reject gaps, double payments, duplicate ids, wrong rows and altered replay receipts."""
from pathlib import Path
from copy import deepcopy
import argparse
import json

from audit_n25_b14_chain import ledger, residual, check_partition, same_branch_result
from n25_outer_search import read, publish
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    output.mkdir()
    groups = [{"id": 0, "centers": 3, "faces": [7], "members": 1},
              {"id": 1, "centers": 4, "faces": [7, 11], "members": 1},
              {"id": 2, "centers": 4, "faces": [7, 13], "members": 1}]
    paid = {0: {"parent_group": 0}, 2: {"parent_group": 2}}
    remaining = {1: groups[1]}
    check_partition(range(3), paid, remaining)
    negatives = []
    for label, p, r in (
        ("missing-parent", {0: paid[0]}, remaining),
        ("paid-and-residual-overlap", {**paid, 1: {"parent_group": 1}}, remaining),
        ("extra-parent", {**paid, 3: {"parent_group": 3}}, remaining),
    ):
        try:
            check_partition(range(3), p, r)
        except AssertionError:
            negatives.append(label)
        else:
            raise AssertionError(("invalid all-parent partition accepted", label))
    duplicate = output / "DUPLICATE-PAYMENTS.jsonl"
    duplicate.write_text('{"parent_group":0}\n{"parent_group":0}\n', encoding="ascii")
    try:
        ledger(duplicate, groups)
    except AssertionError:
        negatives.append("duplicate-payment-id")
    else:
        raise AssertionError("duplicate parent paid")
    wrong = output / "WRONG-ROW.jsonl"
    wrong.write_text(json.dumps({"schema": "control"})+"\n"+json.dumps(
        {"id": 1, "centers": 4, "faces": [7, 13], "members": 1})+"\n", encoding="ascii")
    try:
        residual(wrong, groups, {"schema": "control"})
    except AssertionError:
        negatives.append("residual-row-not-the-parent")
    else:
        raise AssertionError("a different graph substituted for the parent")
    exactpath = ROOT / "n25-paid-hole-controls-20261005-v1/case-0/EXACT.json"
    exact = read(exactpath)
    accepted = deepcopy(exact)
    accepted["pending_complete_leaves"] = 1
    try:
        same_branch_result(exact, accepted)
    except AssertionError:
        negatives.append("altered-exact-replay-receipt")
    else:
        raise AssertionError("altered replay result accepted")
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "all-parent-B14-chain-partition-controls-v1",
        "valid_disjoint_parent_partition_accepted": True,
        "negative_controls_rejected": negatives, "source_sha256": sha(Path(__file__)),
        "auditor_sha256": sha(ROOT / "audit_n25_b14_chain.py"),
        "exact_reference_sha256": sha(exactpath),
        "not_an_independent_B14_family_proof_by_itself": True, "global_optimality_proved": False,
    })
    print("All-parent B14 partition rejection controls PASS:", len(negatives), flush=True)


if __name__ == "__main__":
    main()
