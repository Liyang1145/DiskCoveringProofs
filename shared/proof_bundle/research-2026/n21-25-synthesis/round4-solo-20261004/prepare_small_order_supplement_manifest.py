"""Prepare only finished-parent formal residuals and genuine independently ended supplements."""
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
    ap.add_argument("--base", required=True, type=Path)
    ap.add_argument("--deep", nargs="+", type=Path, required=True)
    ap.add_argument("--include-1915-control", action="store_true")
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    base, output = args.base.resolve(), args.output.resolve()
    assert base.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    reportpath = base / "ACCEPTED/VERIFIED.json"
    report = read(reportpath)
    assert report["verified"]
    assert report["schema"] == "small-order-full-parent-weak-and-complete-filling-disjoint-adoption-v1"
    assert report["source_sha256"] == sha(ROOT / "small_order_parent_fillings.py")
    assert report["full_parent_partition_complete"]
    pipeline = read(base / "PIPELINE-COMPLETED.json")
    assert pipeline["report_sha256"] == sha(reportpath)
    assert pipeline["actual_all_original_workers_and_independent_parent_audit_terminals_observed"]
    additions, bindings = {}, {}
    for deep in args.deep:
        directory = deep.resolve()
        assert directory.is_relative_to(ROOT)
        summarypath = directory / "SUMMARY.json"
        summary = read(summarypath)
        assert (summary["N"], summary["B"]) == (report["N"], report["B"])
        assert summary["source_sha256"] == sha(ROOT / "refine_small_order_completed_workers.py")
        assert summary["all_actual_independent_children_successful_terminals_observed"]
        assert summary["selected_families"] == len(summary["outcomes"])
        for path, digest in summary["frozen_files"].items():
            assert sha(path) == digest
        bindings[str(summarypath)] = sha(summarypath)
        for item in summary["outcomes"]:
            if not item["whole_family_strictly_closed"]:
                continue
            pid = item["parent_index"]
            assert pid not in additions and Path(item["family"]).resolve().is_relative_to(base)
            for label in ("PROPOSE", "REPLAY"):
                terminalpath = directory / f"p{pid}-{label}-TERMINAL.json"
                terminal = read(terminalpath)
                assert terminal["actual_exit_code"] == 0 and terminal["actual_child_terminal_observed"]
                bindings[str(terminalpath)] = sha(terminalpath)
            assert sha(Path(item["proof_path"])) == item["proof_sha256"]
            assert sha(Path(item["exact_path"])) == item["exact_sha256"]
            additions[pid] = {key: item[key] for key in (
                "parent_index", "family", "proof_path", "exact_path", "proof_sha256", "exact_sha256")}
    if args.include_1915_control:
        assert (report["N"], report["B"]) == (24, 16)
        positive = ROOT / "small-order-refinement-controls-v1"
        controls = read(positive / "VERIFIED.json")
        assert controls["verified"] and controls["own_order_real_full_family_strict_positive_separate_process_replayed"]
        family = Path(controls["actual_original_pending_family"]).resolve()
        assert family == base / "batch-000001/parent-0001915"
        pid = 1915
        assert pid not in additions
        additions[pid] = {
            "parent_index": pid, "family": str(family),
            "proof_path": str(positive / "REFINED.json"), "exact_path": str(positive / "EXACT.json"),
            "proof_sha256": sha(positive / "REFINED.json"), "exact_sha256": sha(positive / "EXACT.json")}
        bindings[str(positive / "VERIFIED.json")] = sha(positive / "VERIFIED.json")
    assert additions
    publish(output, {
        "N": report["N"], "B": report["B"], "base_report_sha256": sha(reportpath),
        "additions": [additions[pid] for pid in sorted(additions)],
        "supplement_origin_records_sha256": bindings, "source_sha256": sha(Path(__file__)),
        "formal_parent_residual_identity_and_fresh_math_still_required": True,
        "global_optimality_proved": False})
    print("Own-order real ended supplements manifest prepared:", len(additions),
          "from finished formal parent; adoption still owed", flush=True)


if __name__ == "__main__":
    main()
