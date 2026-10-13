"""Observe the existing B17 root job, then freeze/fill its accepted residual."""
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys

from n25_outer_search import read, publish
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def wait_original(pid, rootstage, output):
    assert os.name == "nt" and type(pid) is int and pid > 0
    script = """
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
$ErrorActionPreference = 'Stop'
$taskProcess = Get-Process -Id TASK_PID
$taskHandle = $taskProcess.Handle
$taskStart = $taskProcess.StartTime.ToUniversalTime().ToFileTimeUtc()
$taskInfo = Get-CimInstance Win32_Process -Filter 'ProcessId = TASK_PID'
if ($null -eq $taskInfo) { throw 'Original root process identity unavailable' }
if ([decimal]::Floor(([decimal]$taskStart) / 10) -ne [decimal]::Floor(([decimal]$taskInfo.CreationDate.ToUniversalTime().ToFileTimeUtc()) / 10)) {
    throw 'Root PID creation identity differs'
}
if ($taskInfo.Name -ne 'python.exe') { throw 'Original root process is not Python' }
if (-not $taskInfo.CommandLine.Contains('run_complete_origin_batches.py')) { throw 'Wrong original root source' }
if (-not $taskInfo.CommandLine.Contains('--output ROOT_STAGE')) { throw 'Wrong original root output' }
$taskCommand = $taskInfo.CommandLine
$taskProcess.WaitForExit()
$taskProcess.Refresh()
[PSCustomObject]@{
    OriginalPid = TASK_PID
    OriginalCreationFileTimeIdentity = $taskStart.ToString()
    OriginalCommandLine = $taskCommand
    ActualExitCode = $taskProcess.ExitCode
    OriginalCachedProcessHandleTerminalObserved = $taskProcess.HasExited
} | ConvertTo-Json -Compress
""".replace("TASK_PID", str(pid)).replace("ROOT_STAGE", rootstage.name)
    result = subprocess.run(
        ["powershell.exe", "-NoProfile", "-NonInteractive", "-Command", script],
        check=True, capture_output=True, encoding="utf8",
        creationflags=subprocess.CREATE_NO_WINDOW)
    terminal = json.loads(result.stdout)
    assert terminal["OriginalPid"] == pid
    assert terminal["OriginalCachedProcessHandleTerminalObserved"]
    publish(output / "ROOT-TERMINAL.json", terminal)
    assert terminal["ActualExitCode"] == 0


def run(command, directory, name):
    with (directory / (name+"-STDOUT.log")).open("xb") as stdout, \
            (directory / (name+"-STDERR.log")).open("xb") as stderr:
        process = subprocess.Popen(
            list(map(str, command)), cwd=str(ROOT), stdout=stdout, stderr=stderr,
            env=dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1"),
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(directory / (name+"-TERMINAL.json"), {
        "child_pid": process.pid, "actual_exit_code": code,
        "independent_process_terminal_observed": True,
        "command": list(map(str, command)), "source_sha256": sha(Path(__file__)),
    })
    assert code == 0, (name, code)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--wait-root-pid", type=int, required=True)
    for name in ("root-stage", "manifest", "terminal", "union", "partition", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    rootstage, manifest, native, union, partition, controls, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("root-stage", "manifest", "terminal", "union", "partition", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (
        rootstage, manifest, native, union, partition, controls, output))
    assert not output.exists()
    assert rootstage.name == "n25-B17-complete-origin-root-force-and-audit-solo-v1"
    assert (read(union)["N"], read(union)["B"], read(union)["unique_necessary_weak_graphs"]) == (25, 17, 289140)
    frozen = {str(path): sha(path) for path in (
        Path(__file__), manifest, native, union, partition, controls,
        ROOT / "run_complete_origin_batches.py", ROOT / "snapshot_complete_origin_pending.py",
        ROOT / "pay_complete_origin_pending.py", ROOT / "audit_complete_origin_fillings.py",
        ROOT / "audit_origin_collar_batches.py", ROOT / "prove_linked_general_collar.py",
        ROOT / "replay_linked_general_collar.py", ROOT / "linked_general_collar_kernel.py",
        ROOT / "refine_linked_collar_leaves.py")}
    output.mkdir()
    publish(output / "PIPELINE-INPUT-BINDINGS.json", {
        "N": 25, "B": 17, "original_root_pid": args.wait_root_pid,
        "frozen_files": frozen, "root_process_not_restarted": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("B17 successor waiting for actual existing root process terminal", args.wait_root_pid,
          "; no root/native restart and no residual payment assumed", flush=True)
    wait_original(args.wait_root_pid, rootstage, output)
    payments = rootstage / "COMPLETE-PAYMENT-AUDIT"
    accepted = read(payments / "VERIFIED.json")
    assert accepted["verified"] and (accepted["N"], accepted["B"], accepted["parent_weak_graphs"]) == (25, 17, 289140)
    assert accepted["source_sha256"] == sha(ROOT / "audit_origin_collar_batches.py")
    for path, digest in frozen.items():
        assert sha(path) == digest
    snapshot = output / "ALL-PENDING-SNAPSHOT.json"
    run([
        sys.executable, "-u", ROOT / "snapshot_complete_origin_pending.py",
        "--manifest", manifest, "--terminal", native, "--union", union,
        "--partition", partition, "--payments", payments, "--output", snapshot],
        output, "SNAPSHOT")
    actual = read(snapshot)
    assert actual["selected_pending_graphs"] == accepted["pending_weak_graphs"]
    print("B17 accepted complete residual frozen:", actual["selected_pending_graphs"],
          "; complete filling stage starts", flush=True)
    fillings = output / "ALL-PENDING-FILLINGS"
    run([
        sys.executable, "-u", ROOT / "pay_complete_origin_pending.py",
        "--snapshot", snapshot, "--controls", controls, "--output", fillings,
        "--workers", 4, "--batch-size", 128, "--limit", 10000, "--force-limit", 31],
        output, "FILLINGS-AND-FULL-PARENT-AUDIT")
    for path, digest in frozen.items():
        assert sha(path) == digest
    finalpath = fillings / "COMPLETE-PAYMENT-AUDIT/VERIFIED.json"
    result = read(finalpath)
    assert result["verified"]
    publish(output / "PIPELINE-COMPLETED.json", {
        "N": 25, "B": 17, "snapshot_sha256": sha(snapshot),
        "final_full_parent_report_sha256": sha(finalpath),
        "root_snapshot_and_filling_terminals_actually_observed": True,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    })
    print("B17 successor complete full-parent filling audit ended;", result.get("counts"), flush=True)


if __name__ == "__main__":
    main()
