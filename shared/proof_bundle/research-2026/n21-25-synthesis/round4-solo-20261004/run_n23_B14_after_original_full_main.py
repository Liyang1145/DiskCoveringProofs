"""Observe the existing full-type main terminal, then adopt four replayed types."""
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


def wait_main(pid, output):
    assert os.name == "nt" and type(pid) is int and pid > 0
    script = r"""
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
$ErrorActionPreference = 'Stop'
$taskProcess = Get-Process -Id TASK_PID
$taskHandle = $taskProcess.Handle
$taskStart = $taskProcess.StartTime.ToUniversalTime().ToFileTimeUtc()
$taskInfo = Get-CimInstance Win32_Process -Filter 'ProcessId = TASK_PID'
if ($null -eq $taskInfo) { throw 'Original full-type main identity unavailable' }
if ([decimal]::Floor(([decimal]$taskStart) / 10) -ne [decimal]::Floor(([decimal]$taskInfo.CreationDate.ToUniversalTime().ToFileTimeUtc()) / 10)) {
    throw 'Original PID creation identity differs'
}
if ($taskInfo.Name -ne 'python.exe') { throw 'Wrong original main image' }
if (-not $taskInfo.CommandLine.Contains('propose_n23_B14_full_residual.py')) { throw 'Wrong original main source' }
if (-not $taskInfo.CommandLine.Contains('--output n23-B14-full1')) { throw 'Wrong original main output' }
$taskCommand = $taskInfo.CommandLine
$taskProcess.WaitForExit()
$taskProcess.Refresh()
[PSCustomObject]@{
    OriginalPid=TASK_PID
    OriginalCreationFileTimeIdentity=$taskStart.ToString()
    OriginalCommandLine=$taskCommand
    ActualExitCode=$taskProcess.ExitCode
    OriginalCachedProcessHandleTerminalObserved=$taskProcess.HasExited
} | ConvertTo-Json -Compress
""".replace("TASK_PID", str(pid))
    result = subprocess.run(
        ["powershell.exe", "-NoProfile", "-NonInteractive", "-Command", script],
        capture_output=True, encoding="utf8", check=True, creationflags=subprocess.CREATE_NO_WINDOW)
    terminal = json.loads(result.stdout)
    assert terminal["OriginalPid"] == pid
    publish(output / "ORIGINAL-MAIN-TERMINAL.json", terminal)
    assert terminal["OriginalCachedProcessHandleTerminalObserved"] and terminal["ActualExitCode"] == 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--wait-pid", type=int, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    sourcepath = ROOT / "n23-B14-complete-source-and-union-reacceptance-20261005-v1/VERIFIED.json"
    original = ROOT / "n23-B14-o2-a"
    previous = ROOT / "n23-B14-full1"
    stage = ROOT / "n23-B14-full4"
    controls = ROOT / "n23-B14-selected-full-controls-v1/VERIFIED.json"
    auditor = ROOT / "audit_n23_B14_selected_full_supplements.py"
    frozen = {str(path): sha(path) for path in (
        Path(__file__), sourcepath, original / "VERIFIED.json", previous / "SUMMARY.json",
        previous / "OUTCOMES.jsonl", controls, auditor,
        ROOT / "propose_n23_B14_full_residual.py", ROOT / "audit_n23_B14_full_residual.py",
        ROOT / "propose_n23_B14_selected_full_supplements.py")}
    output.mkdir()
    publish(output / "PIPELINE-INPUT-BINDINGS.json", {
        "N": 23, "B": 14, "original_main_pid": args.wait_pid,
        "existing_full_type_proposer_and_automatic_audit_not_restarted": True,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    })
    print("N23/B14 final successor awaits actual original main cached handle terminal;",
          "no premature residual payment", flush=True)
    wait_main(args.wait_pid, output)
    parent = previous / "ACCEPTED"
    base = read(parent / "VERIFIED.json")
    assert base["verified"] and base["source_sha256"] == sha(ROOT / "audit_n23_B14_full_residual.py")
    assert base["pending_full_types"] == 4 and base["counts"]["strict-complete-type-force"] == 65206
    full_terminal = read(previous / "AUDIT-TERMINAL.json")
    assert full_terminal["independent_process_terminal_observed"] and full_terminal["actual_exit_code"] == 0
    assert full_terminal["audit_source_sha256"] == sha(ROOT / "audit_n23_B14_full_residual.py")
    # This supplementary producer is separate and normally ends far earlier.
    # Missing/partial reports are refusal, not assumed termination or success.
    supplementary_terminal = read(stage / "REPLAY-TERMINAL.json")
    replayed = read(stage / "REPLAYED/VERIFIED.json")
    assert supplementary_terminal["independent_process_terminal_observed"]
    assert supplementary_terminal["actual_exit_code"] == 0
    assert supplementary_terminal["audit_source_sha256"] == sha(auditor)
    assert replayed["verified"] and replayed["source_sha256"] == sha(auditor)
    assert replayed["strict_complete_type_trees"] == 4 and replayed["proposal_pending_types"] == 0
    assert replayed["actual_parent_adoption"] is None
    for path, digest in replayed["frozen_files"].items():
        assert sha(path) == digest
    for path in (parent / "VERIFIED.json", previous / "AUDIT-TERMINAL.json",
                 stage / "REPLAY-TERMINAL.json", stage / "REPLAYED/VERIFIED.json"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    final = output / "ACCEPTED"
    with (output / "ADOPTION-STDOUT.log").open("xb") as stdout, \
            (output / "ADOPTION-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen(list(map(str, [
            sys.executable, "-u", auditor, "--source", sourcepath, "--original-parent", original,
            "--previous-stage", previous, "--stage", stage, "--controls", controls,
            "--accepted-parent", parent, "--output", final])),
            cwd=str(ROOT), stdout=stdout, stderr=stderr,
            creationflags=subprocess.CREATE_NO_WINDOW)
        code = process.wait()
    publish(output / "ADOPTION-TERMINAL.json", {
        "actual_exit_code": code, "child_pid": process.pid,
        "independent_process_terminal_observed": True, "audit_source_sha256": sha(auditor),
    })
    assert code == 0
    result = read(final / "VERIFIED.json")
    assert result["verified"] and result["actual_parent_adoption"]["pending_full_types"] == 0
    for path, digest in frozen.items():
        assert sha(path) == digest
    publish(output / "PIPELINE-COMPLETED.json", {
        "N": 23, "B": 14, "original_catalog_types": 8277632,
        "final_residual_types": 0, "actual_original_main_and_adoption_terminals_observed": True,
        "final_adoption_sha256": sha(final / "VERIFIED.json"), "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)),
        "source_completeness_and_arbitrary_cover_global_assembly_not_claimed_complete": True,
        "global_optimality_proved": False,
    })
    print("N23/B14 restored original catalogue lower payment chain closed; not N23 global", flush=True)


if __name__ == "__main__":
    main()
