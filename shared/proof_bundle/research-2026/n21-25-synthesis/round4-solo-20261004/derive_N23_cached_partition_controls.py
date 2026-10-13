"""Isolated N23 completion of reboot-interrupted controls; N22 evidence reused later."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from derive_sparse_support_filter import derive

assert __debug__


def main():
    report_path = ROOT / "N23-cached-partition-control-derivation.json"
    assert not report_path.exists()
    record = derive("test_cached_support_origin_partition.py", "test_N23_cached_origin_partition.py", [
        ("    for N in (22, 23):", "    for N in (23,):"),
        ("cached-support-origin-complete-partition-controls-v1", "cached-support-origin-N23-partition-controls-v1"),
        ("all_four_complete_small_family_partitions_paid", "all_two_complete_N23_partitions_paid"),
    ])
    publish(report_path, {
        "verified": True, "schema": "isolated-N23-cached-partition-control-derivation-v1",
        "file": record, "all_actual_terminal_union_and_removed_graph_checks_unchanged": True,
        "already_completed_N22_cases_not_restarted": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
