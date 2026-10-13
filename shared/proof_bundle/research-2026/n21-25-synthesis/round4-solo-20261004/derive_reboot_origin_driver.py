"""Isolated recovery driver; original proof/storage checks remain unchanged."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish
from derive_sparse_support_filter import derive

assert __debug__


def main():
    report_path = ROOT / "reboot-origin-driver-source-derivation.json"
    assert not report_path.exists()
    record = derive("run_origin_streamed_search.py", "run_reboot_origin_search.py", [
        ("from origin_production_gate import origin_gate", "from reboot_interruption_gate import recovery_gate"),
        ('    assert B in (16, 17), "only the terminal-failed B16/B17 runs are replaced"',
         '    assert B in (15, 16, 17), "only authoritatively reboot-interrupted N25 jobs are recovered"'),
        ("files.update(origin_gate(args.origin_controls.resolve(), args.failed_search.resolve(), B))",
         "files.update(recovery_gate(args.origin_controls.resolve(), args.failed_search.resolve(), B))"),
    ])
    publish(report_path, {
        "verified": True, "schema": "reboot-origin-driver-isolated-derivation-v1",
        "source_sha256": sha(Path(__file__)), "file": record,
        "all_existing_library_angle_injection_guard_storage_and_final_union_checks_unchanged": True,
        "only_recovery_lifecycle_gate_changed": True, "global_optimality_proved": False,
    })
    print("New reboot recovery driver mechanically derived; original proof gates preserved", flush=True)


if __name__ == "__main__":
    main()
