"""Add the one actual own-core family to ended strict supplemental sources."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    strictpath, output = args.strict.resolve(), args.output.resolve()
    assert strictpath.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    data = read(strictpath)
    assert (data["N"], data["B"]) == (24, 15)
    assert data["source_sha256"] == sha(ROOT / "prepare_small_order_supplement_manifest.py")
    base = ROOT / "n24-B15-f1"
    assert data["base_report_sha256"] == sha(base / "ACCEPTED/VERIFIED.json")
    assert len(data["additions"]) == 92
    for path, digest in data["supplement_origin_records_sha256"].items():
        assert sha(path) == digest
    additions = [{**item, "kind": "strict-complete-family-refinement"} for item in data["additions"]]
    assert len({item["parent_index"] for item in additions}) == 92
    assert all(item["parent_index"] != 29688 for item in additions)
    proofpath = ROOT / "n24-B15-p29688-finer-mixed1.json"
    exactpath = ROOT / "n24-B15-p29688-finer-mixed1-EXACT.json"
    corecontrols = ROOT / "n24-own-core-transport-controls-v1/VERIFIED.json"
    exact = read(exactpath)
    assert exact["verified"] and exact["whole_completion_family_paid_strict_or_same_root"]
    assert exact["pending_complete_leaves"] == exact["unsearched_frontier_nodes"] == 0
    assert not exact["whole_family_strictly_closed"]
    assert exact["proposal_sha256"] == sha(proofpath)
    assert exact["source_sha256"] == sha(ROOT / "prove_n24_core_and_finer_family.py")
    for path, digest in exact["frozen_files"].items():
        assert sha(path) == digest
    additions.append({
        "kind": "own-N24-complete-family-strict-and-same-root-core", "parent_index": 29688,
        "family": str(base / "batch-000120/parent-0029688"),
        "proof_path": str(proofpath), "exact_path": str(exactpath),
        "proof_sha256": sha(proofpath), "exact_sha256": sha(exactpath),
        "own_core_controls": str(corecontrols), "own_core_controls_sha256": sha(corecontrols)})
    bindings = dict(data["supplement_origin_records_sha256"])
    for path in (strictpath, proofpath, exactpath, corecontrols, Path(__file__)):
        bindings[str(path)] = sha(path)
    publish(output, {
        "N": 24, "B": 15, "base_report_sha256": data["base_report_sha256"],
        "additions": sorted(additions, key=lambda item: item["parent_index"]),
        "supplement_origin_records_sha256": bindings,
        "source_sha256": sha(Path(__file__)), "old_mixed_core_never_counted_as_strict": True,
        "actual_formal_parent_disjoint_adoption_still_required": True,
        "global_optimality_proved": False})
    print("N24 B15 all formal-parent supplements prepared:92 strict +1 own mixed;",
          "actual full-parent adoption still owed", flush=True)


if __name__ == "__main__":
    main()
