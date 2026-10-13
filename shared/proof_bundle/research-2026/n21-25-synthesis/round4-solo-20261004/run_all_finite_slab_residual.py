"""Sequential proposal/replay/filling work for ALL residual rows of one finite slab.

No native full search is started, stopped, or changed. Stage summaries never
substitute for the separate final all-slab-row payment audit.
"""
from pathlib import Path
import argparse
import subprocess
import sys
import threading

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged

assert __debug__


def run_stage(script, arguments, output, label):
    log_path = output / (label+"-OUTPUT.log")
    with log_path.open("xb") as log:
        process = subprocess.Popen([sys.executable, str(script), *map(str, arguments)],
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   creationflags=subprocess.CREATE_NO_WINDOW)
        publish(output / (label+"-LAUNCH.json"), {
            "owned_windows_python_pid": process.pid, "script": script.name,
            "source_sha256": sha(script), "arguments": list(map(str, arguments)),
        })
        def collect():
            for line in iter(process.stdout.readline, b""):
                log.write(line);log.flush()
        collector = threading.Thread(target=collect, daemon=True)
        collector.start()
        code = process.wait()
        collector.join(timeout=30)
        assert not collector.is_alive()
        process.stdout.close()
    publish(output / (label+"-TERMINAL.json"), {
        "actual_exit_code": code, "native_or_python_terminal_observed": True,
        "source_sha256": sha(script), "output_log_sha256": sha(log_path),
    })
    assert code == 0, (label, code, "partial outputs remain evidence, not a completed stage")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--payments", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    args.payments, args.output = args.payments.resolve(), args.output.resolve()
    assert args.payments.is_relative_to(ROOT) and args.output.is_relative_to(ROOT)
    assert not args.output.exists()
    parent_path = args.payments / "VERIFIED.json"
    parent = read(parent_path)
    assert parent["verified"] and parent["schema"] == "independent-finite-origin-slab-combined-payments-v1"
    assert parent["pending_rows"] > 0 and parent["not_a_complete_competitor_family_or_union"]
    controls_path = ROOT / "n25-linked-general-collar-controls-20261005-v1/VERIFIED.json"
    controls = read(controls_path)
    assert controls["verified"] and controls["known_attaining_candidate_not_strictly_paid"]
    files = dict(parent["files_relative_to_workspace"])
    for path in (Path(__file__), parent_path, controls_path,
                 ROOT / "snapshot_combined_slab_pending.py", ROOT / "probe_family_discovery.py",
                 ROOT / "replay_family_discovery.py", ROOT / "pay_finite_discovery_fillings.py"):
        bind(files, path)
    unchanged(files)
    args.output.mkdir()
    publish(args.output / "INPUT-BINDINGS.json", {
        "N": parent["N"], "B": parent["B"], "finite_parent_pending_rows": parent["pending_rows"],
        "files_relative_to_workspace": files, "not_a_complete_competitor_family_or_union": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    snapshot_path = args.output / "ALL-PENDING-SNAPSHOT.json"
    receipt_path, replay_path = args.output / "STRICT/SUMMARY.json", args.output / "STRICT-EXACT.json"
    for script, arguments, label in (
        (ROOT / "snapshot_combined_slab_pending.py",
         ["--payments", args.payments, "--output", snapshot_path], "SNAPSHOT"),
        (ROOT / "probe_family_discovery.py",
         ["--snapshot", snapshot_path, "--output", args.output / "STRICT",
          "--count", parent["pending_rows"], "--limit", 1], "STRICT"),
        (ROOT / "replay_family_discovery.py",
         ["--snapshot", snapshot_path, "--receipt", receipt_path, "--output", replay_path], "STRICT-REPLAY"),
    ):
        print("Finite ALL-residual stage dispatched:", label, flush=True)
        run_stage(script, arguments, args.output, label)
    replay = read(replay_path)
    assert replay["verified"] and replay["totals"].get("excluded", 0)+replay["totals"].get("pending", 0) == parent["pending_rows"]
    print("Finite ALL-residual strict stage accepted:", replay["totals"], flush=True)
    if replay["totals"].get("pending", 0):
        print("Finite ALL-residual completion stage dispatched", flush=True)
        run_stage(ROOT / "pay_finite_discovery_fillings.py", [
            "--snapshot", snapshot_path, "--receipt", receipt_path, "--replay", replay_path,
            "--controls", controls_path, "--output", args.output / "FILLINGS", "--limit", 10000,
        ], args.output, "FILLINGS")
    unchanged(files)
    publish(args.output / "STAGES-VERIFIED.json", {
        "verified": True, "schema": "all-finite-slab-residual-proposal-and-replay-stages-v1",
        "N": parent["N"], "B": parent["B"], "finite_source_pending_rows": parent["pending_rows"],
        "strict_graph_totals": replay["totals"],
        "snapshot_sha256": sha(snapshot_path), "strict_receipt_sha256": sha(receipt_path),
        "strict_replay_sha256": sha(replay_path),
        "filling_report_sha256": (sha(args.output / "FILLINGS/VERIFIED.json")
                                  if replay["totals"].get("pending", 0) else None),
        "final_all_slab_payment_and_overlap_audit_still_required": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "not_a_complete_competitor_family_or_union": True, "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
