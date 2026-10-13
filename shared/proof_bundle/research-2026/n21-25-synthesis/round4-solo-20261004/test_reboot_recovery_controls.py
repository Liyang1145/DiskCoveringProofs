"""Read-only recovery lifecycle controls, including real duplicate-job rejection."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from reboot_interruption_gate import recovery_gate, assert_no_live_boundary, current_state, PREVIOUS_NAMES, RECORD_NAME

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    record_path = ROOT / RECORD_NAME / "VERIFIED.json"
    record = read(record_path)
    assert record["verified"] and record["actual_old_native_exit_code_unknown"]
    assert all(row["actual_native_exit_code"] is None for row in record["searches"])
    origin_path = ROOT / "n25-origin-collar-controls-20261005-v1/VERIFIED.json"
    linux_text, boot_utc, boot_timestamp, windows_text = current_state()
    assert boot_utc == record["windows_last_boot_utc"]
    files = recovery_gate(origin_path, ROOT / PREVIOUS_NAMES[16], 16)
    rejected = []
    for label, previous, B in (
        ("wrong-old-directory", ROOT / PREVIOUS_NAMES[15], 16),
        ("unregistered-boundary", ROOT / PREVIOUS_NAMES[16], 25),
        ("actual-live-B15-duplicate", ROOT / PREVIOUS_NAMES[15], 15),
        ("actual-live-B17-duplicate", ROOT / PREVIOUS_NAMES[17], 17),
    ):
        try:
            recovery_gate(origin_path, previous, B)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("unsafe lifecycle request accepted", label))
    for name in ("peel_origin_streamed_collar-linux", "peel_cached_support_origin_collar-linux"):
        text = "  PID COMMAND\n123 ./"+name+" 25 16 fresh/output.json 10000000\n"
        try:
            assert_no_live_boundary(text, 16)
        except AssertionError:
            rejected.append("synthetic-live-"+name)
        else:
            raise AssertionError("live new/old binary not rejected")
        assert_no_live_boundary(text, 15)
    assert_no_live_boundary("PID COMMAND\n123 ./peel_cached_support_origin_collar-linux 23 16 control\n", 16)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    for path in (Path(__file__), record_path, ROOT / "reboot_interruption_gate.py",
                 ROOT / "run_reboot_origin_search.py", ROOT / "reboot-origin-driver-source-derivation.json"):
        bind(files, path)
    unchanged(files)
    publish(output, {
        "verified": True, "schema": "read-only-machine-reboot-recovery-lifecycle-controls-v1",
        "current_boot_equals_recorded_reboot": True,
        "B16_recovery_readiness_reaccepted_without_starting_a_search": True,
        "actual_B15_B17_duplicate_recovery_requests_rejected": True,
        "negative_controls_rejected": rejected,
        "old_actual_exit_codes_remain_unknown_not_fabricated": True,
        "no_process_signal_or_file_delete_performed": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "global_optimality_proved": False,
    })
    print("Reboot recovery controls PASS: B16 readiness;",
          len(rejected), "rejections including two actual live jobs", flush=True)


if __name__ == "__main__":
    main()
