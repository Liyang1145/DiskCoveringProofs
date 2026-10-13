"""Actual mixed family complete replay and formal-parent scope refusal controls."""
from pathlib import Path
from copy import deepcopy
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from audit_n24_mixed_parent_supplements import mixed_supplement, manifest_gate

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    base = ROOT / "n24-B15-f1"
    expected = {}
    with (base / "ACCEPTED/PENDING.jsonl").open(encoding="ascii") as stream:
        for line in stream:
            item = json.loads(line, object_pairs_hook=no_duplicate_keys)
            expected[item["parent_index"]] = item
    item = {
        "kind": "own-N24-complete-family-strict-and-same-root-core", "parent_index": 29688,
        "family": str(base / "batch-000120/parent-0029688"),
        "proof_path": str(ROOT / "n24-B15-p29688-finer-mixed1.json"),
        "exact_path": str(ROOT / "n24-B15-p29688-finer-mixed1-EXACT.json"),
        "proof_sha256": sha(ROOT / "n24-B15-p29688-finer-mixed1.json"),
        "exact_sha256": sha(ROOT / "n24-B15-p29688-finer-mixed1-EXACT.json"),
        "own_core_controls": str(ROOT / "n24-own-core-transport-controls-v1/VERIFIED.json"),
        "own_core_controls_sha256": sha(ROOT / "n24-own-core-transport-controls-v1/VERIFIED.json")}
    result = mixed_supplement(item, expected[29688])
    assert result["nonstrict_complete_leaves"] == 2
    manifest = {"N": 24, "B": 15, "base_report_sha256": sha(base / "ACCEPTED/VERIFIED.json"),
                "additions": [item]}
    assert list(manifest_gate(manifest, manifest["base_report_sha256"], expected)) == [29688]
    refused = []
    for field, value in (("N", 25), ("B", 16), ("base_report_sha256", "0"*64)):
        bad = deepcopy(manifest)
        bad[field] = value
        try:
            manifest_gate(bad, manifest["base_report_sha256"], expected)
        except (AssertionError, KeyError):
            refused.append(field)
        else:
            raise AssertionError("wrong mixed parent scope accepted: "+field)
    for name, change in (
        ("duplicate-parent", lambda m: m["additions"].append(deepcopy(m["additions"][0]))),
        ("unpaid-set-only", lambda m: m["additions"][0].update(parent_index=0)),
        ("core-cannot-pay-other-parent", lambda m: m["additions"][0].update(parent_index=next(p for p in expected if p != 29688))),
        ("core-recast-as-strict", lambda m: m["additions"][0].update(kind="strict-complete-family-refinement"))):
        bad = deepcopy(manifest)
        change(bad)
        try:
            manifest_gate(bad, manifest["base_report_sha256"], expected)
        except (AssertionError, KeyError):
            refused.append(name)
        else:
            raise AssertionError("illegal actual parent adoption accepted: "+name)
    for field, value in (("proof_sha256", "0"*64), ("exact_sha256", "0"*64),
                         ("own_core_controls_sha256", "0"*64)):
        bad = deepcopy(item)
        bad[field] = value
        try:
            mixed_supplement(bad, expected[29688])
        except (AssertionError, KeyError):
            refused.append(field)
        else:
            raise AssertionError("unbound mixed math premise accepted: "+field)
    assert len(refused) == 10
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N24-formal-mixed-parent-supplement-controls-v1",
        "actual_mixed_whole_family_mathematics_freshly_replayed": True,
        "negative_mixed_parent_controls_rejected": refused,
        "no_control_subset_mistaken_for_full_formal_parent_adoption": True,
        "source_sha256": sha(Path(__file__)),
        "audit_source_sha256": sha(ROOT / "audit_n24_mixed_parent_supplements.py"),
        "actual_formal_parent_report_sha256": sha(base / "ACCEPTED/VERIFIED.json"),
        "positive_exact_report_sha256": item["exact_sha256"], "global_optimality_proved": False})
    print("N24 formal mixed-parent controls accepted:actual whole-family replay +10 refusals",
          "; not a full parent payment", flush=True)


if __name__ == "__main__":
    main()
