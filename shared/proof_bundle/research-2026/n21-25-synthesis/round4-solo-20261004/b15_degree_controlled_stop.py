"""Exact owned-process identity and evidence-preserving B15 replacement lifecycle."""
from pathlib import Path
import argparse
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parent
from n25_outer_search import read, publish, bind, unchanged, WORK
from stream_catalog import sha
from test_outer_collar import WSL, linux_path

assert __debug__
RECORD_NAME = "n25-B15-controlled-degree-replacement-20261005-v1"


def invoke(arguments):
    result = subprocess.run([WSL, "--distribution", "Ubuntu2204", "--exec", *arguments],
                            capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    assert result.returncode == 0, (arguments, result.returncode, result.stderr)
    return result


def inspect_owned(previous):
    assert previous.resolve() == ROOT / "n25-B15-origin-streamed-search-reboot-20261005-v1"
    inputs = read(previous / "INPUT-BINDINGS.json")
    identity = read(previous / "LINUX-NATIVE-IDENTITY.json")
    launch = read(previous / "WSL-LAUNCH.json")
    assert (inputs["N"], inputs["B"]) == (25, 15)
    assert launch["command"] == inputs["command"]
    assert launch["owned_wsl_proxy_pid"] == identity["owned_wsl_proxy_pid"]
    binary = ROOT / "peel_origin_streamed_collar-linux"
    assert sha(binary) == identity["native_binary_sha256"]
    assert sha(binary) == inputs["files_relative_to_workspace"][binary.relative_to(WORK).as_posix()]
    unchanged(inputs["files_relative_to_workspace"])
    pid = identity["linux_native_pid"]
    assert type(pid) is int and pid > 1
    assert identity["binary_linux_path"] == linux_path(binary)
    command = inputs["command"]
    expected = command[command.index("./peel_origin_streamed_collar-linux"):]
    assert expected[:3] == ["./peel_origin_streamed_collar-linux", "25", "15"]
    assert expected[3].startswith(previous.name+"/")
    assert len(expected) == 15 and expected[-3:] == ["4058615", "100000", "1"]
    assert expected[8:11] == ["0", "dfs", "-"]
    actual = invoke(["/bin/cat", f"/proc/{pid}/cmdline"]).stdout.split(b"\0")
    assert actual[-1] == b""
    actual = [value.decode("utf8") for value in actual[:-1]]
    executable = invoke(["/usr/bin/readlink", "-f", f"/proc/{pid}/exe"]).stdout.decode("utf8").strip()
    directory = invoke(["/usr/bin/readlink", "-f", f"/proc/{pid}/cwd"]).stdout.decode("utf8").strip()
    assert actual == expected and executable == linux_path(binary) and directory == linux_path(ROOT)
    stat = invoke(["/bin/cat", f"/proc/{pid}/stat"]).stdout.decode("utf8")
    assert int(stat.split(" ", 1)[0]) == pid
    start_time = int(stat.rsplit(")", 1)[1].split()[19])
    assert not (previous / "NATIVE-TERMINAL.json").exists()
    assert not (previous / "SUMMARY.json").exists()
    return {
        "linux_native_pid": pid, "linux_starttime_ticks": start_time, "actual_native_cmdline": actual,
        "actual_linux_executable": executable, "actual_linux_cwd": directory,
        "native_binary_sha256": sha(binary), "owned_wsl_proxy_pid": launch["owned_wsl_proxy_pid"],
        "old_input_bindings_sha256": sha(previous / "INPUT-BINDINGS.json"),
        "old_native_identity_sha256": sha(previous / "LINUX-NATIVE-IDENTITY.json"),
        "old_search_relative_to_workspace": previous.relative_to(ROOT).as_posix(),
        "owned_process_identity_independently_checked": True,
    }


def replacement_readiness(previous):
    assert previous.resolve() == ROOT / "n25-B15-origin-streamed-search-reboot-20261005-v1"
    record = ROOT / RECORD_NAME
    pre, signal = read(record / "PRE-SIGNAL.json"), read(record / "SIGNAL-RESULT.json")
    assert pre["owned_process_identity_independently_checked"]
    assert pre["source_sha256"] == sha(Path(__file__))
    assert signal["exact_owned_native_SIGTERM_sent"] and signal["signal_command_exit_code"] == 0
    terminal = read(previous / "NATIVE-TERMINAL.json")
    assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] != 0
    assert terminal["linux_native_pid"] == pre["linux_native_pid"]
    assert terminal["owned_wsl_proxy_pid"] == pre["owned_wsl_proxy_pid"]
    assert terminal["native_log_sha256"] == sha(previous / "NATIVE-STDERR.log")
    assert terminal["manifest_sha256"] is None and not (previous / "SUMMARY.json").exists()
    assert pre["old_input_bindings_sha256"] == sha(previous / "INPUT-BINDINGS.json")
    assert pre["old_native_identity_sha256"] == sha(previous / "LINUX-NATIVE-IDENTITY.json")
    snapshot = invoke(["/bin/ps", "-eo", "pid,args"]).stdout.decode("utf8", errors="replace")
    assert "PID COMMAND" in snapshot
    assert not any(re.search(r"\./peel_\S*collar-linux\s+25\s+15(?:\s|$)", line)
                   for line in snapshot.splitlines()), "another N25/B15 enumerator is still alive"
    files = {}
    inputs = read(previous / "INPUT-BINDINGS.json")
    unchanged(inputs["files_relative_to_workspace"])
    for path in (record / "PRE-SIGNAL.json", record / "SIGNAL-RESULT.json",
                 previous / "INPUT-BINDINGS.json", previous / "LINUX-NATIVE-IDENTITY.json",
                 previous / "NATIVE-TERMINAL.json", previous / "NATIVE-STDERR.log", Path(__file__)):
        bind(files, path)
    return files


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--previous", type=Path, required=True)
    ap.add_argument("--record", type=Path, required=True)
    args = ap.parse_args()
    previous, record = args.previous.resolve(), args.record.resolve()
    assert record == ROOT / RECORD_NAME and not record.exists()
    from b15_origin_replacement_gate import b15_origin_controls_gate
    files = b15_origin_controls_gate(ROOT / "n25-origin-collar-controls-20261005-v1/VERIFIED.json")
    specific_path = ROOT / "n25-B15-origin-replacement-controls-20261005-v1/VERIFIED.json"
    specific = read(specific_path)
    assert specific["verified"] and specific["schema"] == "B15-origin-replacement-controls-v1"
    assert specific["source_sha256"] == sha(ROOT / "test_b15_origin_replacement.py")
    assert specific["all_complete_B15_small_sets_equal"] and specific["all_N25_seed_results_paid_or_retained"]
    unchanged(specific["files_relative_to_workspace"])
    from pending_degree_production_gate import production_gate
    files.update(production_gate(
        ROOT / "n25-B15-offline-contracted-union27-library-20261005-v1/LIBRARY.json",
        ROOT / "n25-B15-union27-sparse-map-controls-20261005-v1/VERIFIED.json",
        ROOT / "n25-B15-union27-eight-sparse-guard-controls-20261005-v1/VERIFIED.json", 15))
    checked = inspect_owned(previous)
    record.mkdir()
    publish(record / "PRE-SIGNAL.json", {
        **checked, "source_sha256": sha(Path(__file__)), "specific_controls_sha256": sha(specific_path),
        "mathematical_origin_controls_sha256": sha(ROOT / "n25-origin-collar-controls-20261005-v1/VERIFIED.json"),
        "reason": "controlled earlier-degree replacement after full B15 degree and origin controls",
        "degree_controls_sha256": sha(ROOT / "n25-pending-degree-upper-full-controls-20261005-v1/VERIFIED.json"),
        "new_driver_derivation_sha256": sha(ROOT / "b15-degree-replacement-source-derivation.json"),
        "not_an_exhaustive_or_memory_failure_termination": True,
        "all_old_files_preserved": True, "old_prefix_not_a_resumable_or_complete_catalog": True,
    })
    repeated = inspect_owned(previous)
    assert repeated == checked, "owned identity changed between checks"
    result = invoke(["/bin/kill", "-TERM", str(checked["linux_native_pid"])])
    publish(record / "SIGNAL-RESULT.json", {
        "exact_owned_native_SIGTERM_sent": True, "signal_command_exit_code": result.returncode,
        "linux_native_pid": checked["linux_native_pid"],
        "actual_old_process_terminal_still_must_be_collected": True,
        "all_old_files_preserved": True, "global_optimality_proved": False,
    })
    print("Exact owned reboot B15 native signalled for verified degree replacement:",
          checked["linux_native_pid"], "; old terminal still required; all files preserved", flush=True)


if __name__ == "__main__":
    main()
