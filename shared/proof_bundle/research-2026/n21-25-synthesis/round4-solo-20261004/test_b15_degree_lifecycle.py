"""Read-only live identity plus simulated refusal controls; sends no signal."""
from pathlib import Path
from copy import deepcopy
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from pending_degree_production_gate import production_gate, driver_derivation_gate
import b15_degree_controlled_stop as stop

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    library_path = ROOT / "n25-B15-offline-contracted-union27-library-20261005-v1/LIBRARY.json"
    maps_path = ROOT / "n25-B15-union27-sparse-map-controls-20261005-v1/VERIFIED.json"
    guard_path = ROOT / "n25-B15-union27-eight-sparse-guard-controls-20261005-v1/VERIFIED.json"
    files = production_gate(library_path, maps_path, guard_path, 15)
    previous = ROOT / "n25-B15-origin-streamed-search-reboot-20261005-v1"
    checked = stop.inspect_owned(previous)
    assert checked["owned_process_identity_independently_checked"]
    old_bindings_sha = sha(previous / "INPUT-BINDINGS.json")
    old_identity_sha = sha(previous / "LINUX-NATIVE-IDENTITY.json")
    output.mkdir()
    publish(output / "ACTUAL-LIVE-IDENTITY.json", checked)
    rejected = []
    for name, path in (
        ("wrong-old-preboot-directory", ROOT / "n25-B15-streamed-eight-sparse-search-20261005-v1"),
        ("wrong-boundary-live-directory", ROOT / "n25-B17-origin-streamed-search-reboot-20261005-v1"),
    ):
        try:
            stop.inspect_owned(path)
        except AssertionError:
            rejected.append(name)
        else:
            raise AssertionError(("wrong target admitted", name))
    for name, path, boundary in (
        ("wrong-boundary-for-new-gate", library_path, 16),
        ("old-nine-library-in-new-gate", ROOT / "n25-B15-new-sparse-library-20261005-v1/LIBRARY.json", 15),
    ):
        try:
            production_gate(path, maps_path, guard_path, boundary)
        except AssertionError:
            rejected.append(name)
        else:
            raise AssertionError(("wrong production input admitted", name))
    original_invoke = stop.invoke
    pid = checked["linux_native_pid"]
    actual_stat = original_invoke(["/bin/cat", f"/proc/{pid}/stat"]).stdout
    signal_attempts = []

    def fake_proc_reader(label):
        def invoke(arguments):
            assert arguments[0] != "/bin/kill", "a refusal test attempted to signal"
            if arguments == ["/bin/cat", f"/proc/{pid}/cmdline"]:
                command = list(checked["actual_native_cmdline"])
                replacements = {
                    "wrong-program": (0, "./peel_unrelated_collar-linux"),
                    "wrong-N": (1, "24"), "wrong-B": (2, "16"),
                    "wrong-output": (3, "another-directory/MANIFEST.json"),
                    "wrong-sparse-library": (11, "another-library/OBSTACLES.tsv"),
                    "wrong-origin-flag": (14, "0"),
                }
                if label in replacements:
                    index, value = replacements[label]
                    command[index] = value
                stdout = b"\0".join(value.encode("utf8") for value in command)+b"\0"
            elif arguments == ["/usr/bin/readlink", "-f", f"/proc/{pid}/exe"]:
                value = "/tmp/unrelated-program" if label == "wrong-executable" else checked["actual_linux_executable"]
                stdout = (value+"\n").encode("utf8")
            elif arguments == ["/usr/bin/readlink", "-f", f"/proc/{pid}/cwd"]:
                value = "/tmp/unrelated-directory" if label == "wrong-cwd" else checked["actual_linux_cwd"]
                stdout = (value+"\n").encode("utf8")
            elif arguments == ["/bin/cat", f"/proc/{pid}/stat"]:
                stdout = (str(pid+1).encode("ascii")+actual_stat[actual_stat.index(b" "):]
                          if label == "wrong-stat-PID" else actual_stat)
            else:
                raise AssertionError(("unexpected simulated request", arguments))
            return subprocess.CompletedProcess(arguments, 0, stdout, b"")
        return invoke

    try:
        for name in ("wrong-program", "wrong-N", "wrong-B", "wrong-output", "wrong-sparse-library",
                     "wrong-origin-flag", "wrong-executable", "wrong-cwd", "wrong-stat-PID"):
            stop.invoke = fake_proc_reader(name)
            try:
                stop.inspect_owned(previous)
            except AssertionError:
                rejected.append("simulated-"+name)
            else:
                raise AssertionError(("wrong process identity admitted", name))
    finally:
        stop.invoke = original_invoke
    # Execute the real pre-signal path against a simulated identity change in
    # a distinct test record directory. No production stop record is written.
    original_inspect, original_record, original_argv = stop.inspect_owned, stop.RECORD_NAME, sys.argv
    calls = []

    def changing_identity(path):
        assert path.resolve() == previous
        value = deepcopy(checked)
        calls.append(path)
        if len(calls) > 1:
            value["linux_starttime_ticks"] += 1
        return value

    def no_signal(arguments):
        if arguments[0] == "/bin/kill":
            signal_attempts.append(arguments)
            raise AssertionError("unexpected signal request in read-only controls")
        return original_invoke(arguments)

    try:
        stop.inspect_owned = changing_identity
        stop.invoke = no_signal
        stop.RECORD_NAME = output.relative_to(ROOT).as_posix()+"/SIMULATED-IDENTITY-CHANGE"
        record = ROOT / stop.RECORD_NAME
        sys.argv = ["test-owned-stop", "--previous", str(previous), "--record", str(record)]
        try:
            stop.main()
        except AssertionError as error:
            assert "owned identity changed between checks" in str(error)
            rejected.append("simulated-process-reused-between-two-identity-checks")
        else:
            raise AssertionError("changed process identity reached signalling")
        assert len(calls) == 2 and not signal_attempts
        assert (record / "PRE-SIGNAL.json").exists() and not (record / "SIGNAL-RESULT.json").exists()
        bind(files, record / "PRE-SIGNAL.json")
    finally:
        stop.inspect_owned, stop.invoke, stop.RECORD_NAME, sys.argv = (
            original_inspect, original_invoke, original_record, original_argv)
    try:
        stop.replacement_readiness(previous)
    except FileNotFoundError:
        rejected.append("real-live-job-with-no-stop-record-not-ready-for-replacement")
    else:
        raise AssertionError("a live job with no actual stopping record became replaceable")
    assert stop.inspect_owned(previous) == checked
    assert sha(previous / "INPUT-BINDINGS.json") == old_bindings_sha
    assert sha(previous / "LINUX-NATIVE-IDENTITY.json") == old_identity_sha
    assert not (ROOT / original_record).exists()
    assert not (previous / "NATIVE-TERMINAL.json").exists()
    for path in (Path(__file__), output / "ACTUAL-LIVE-IDENTITY.json",
                 previous / "INPUT-BINDINGS.json", previous / "LINUX-NATIVE-IDENTITY.json",
                 previous / "WSL-LAUNCH.json", ROOT / "b15_degree_controlled_stop.py",
                 driver_derivation_gate(), library_path, maps_path, guard_path):
        bind(files, path)
    unchanged(files)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "B15-current-degree-replacement-readonly-lifecycle-controls-v1",
        "full_production_controls_and_four_complete_B15_sets_reaccepted": True,
        "actual_live_identity_checked_before_and_after_controls": checked,
        "negative_controls_rejected": rejected,
        "process_identity_refusals_with_simulated_proc_data_not_actual_failures": True,
        "simulated_pre_signal_record_never_a_production_stop_record": True,
        "actual_signals_sent": 0, "new_production_jobs_launched": 0,
        "all_current_old_inputs_and_identity_bytes_unchanged": True,
        "actual_stop_terminal_and_absence_of_duplicate_native_still_required": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "global_optimality_proved": False,
    })
    print("Current B15 degree lifecycle controls PASS:", len(rejected),
          "refusals; no signal; old live identity unchanged", flush=True)


if __name__ == "__main__":
    main()
