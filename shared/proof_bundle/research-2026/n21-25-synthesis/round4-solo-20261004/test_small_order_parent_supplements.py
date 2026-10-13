"""Actual full-family positive and identity/status/order refusals; no full adoption."""
from pathlib import Path
from copy import deepcopy
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish
from stream_catalog import sha
from audit_small_order_parent_supplements import source_identity, supplement

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    family = ROOT / "n24-B16-f1/batch-000001/parent-0001915"
    positive = ROOT / "small-order-refinement-controls-v1"
    collar = read(family / "INPUT-COLLAR.json")
    row = {
        "parent_index": 1915, "centers": collar["centers"], "faces": collar["faces"],
        "status": "pending-complete-family", "not_an_exclusion": True}
    item = {
        "parent_index": 1915, "family": str(family),
        "proof_path": str(positive / "REFINED.json"), "exact_path": str(positive / "EXACT.json"),
        "proof_sha256": sha(positive / "REFINED.json"), "exact_sha256": sha(positive / "EXACT.json")}
    result = supplement(item, row, 24, 16)
    assert result["parent_index"] == 1915
    refused = []
    for field, value in (
        ("N", 25), ("B", 15), ("actual_source_parent_index", 1916),
        ("centers", collar["centers"]-1), ("faces", collar["faces"][:-1])):
        wrong = deepcopy(collar)
        wrong[field] = value
        try:
            source_identity(row, wrong, 24, 16)
        except (AssertionError, KeyError):
            refused.append(field)
        else:
            raise AssertionError("bad actual source identity accepted: "+field)
    for field, value in (("status", "strict-complete-family"), ("not_an_exclusion", False)):
        wrong = deepcopy(row)
        wrong[field] = value
        try:
            source_identity(wrong, collar, 24, 16)
        except AssertionError:
            refused.append(field)
        else:
            raise AssertionError("wrong current residual accepted: "+field)
    wrong = deepcopy(item)
    wrong["proof_sha256"] = "0"*64
    try:
        supplement(wrong, row, 24, 16)
    except AssertionError:
        refused.append("modified-complete-family-proof")
    else:
        raise AssertionError("unbound whole-family proof accepted")
    assert len(refused) == 8
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "small-order-formal-parent-whole-family-supplement-controls-v1",
        "real_whole_family_positive_freshly_replayed": True, "refusals": refused,
        "control_graph_not_mistaken_for_finished_formal_full_parent": True,
        "source_sha256": sha(Path(__file__)),
        "audit_source_sha256": sha(ROOT / "audit_small_order_parent_supplements.py"),
        "positive_exact_report_sha256": sha(positive / "EXACT.json"),
        "global_optimality_proved": False})
    print("Own-order full-parent supplement identity controls passed:8 refusals,",
          "actual complete-family replay; no parent scope claim", flush=True)


if __name__ == "__main__":
    main()
