"""Observe actual existing audit/deep-worker terminals, then merge the whole source."""
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


def wait_existing(auditpid, deeppid, output):
    assert os.name == "nt" and type(auditpid) is int and type(deeppid) is int
    assert auditpid > 0 and deeppid > 0 and auditpid != deeppid
    script = r"""
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
$ErrorActionPreference = 'Stop'
$taskSpecs = @(
    @{Pid=AUDIT_PID;Source='audit_library_parent_fillings.py';Output='--output n25-B16-f1-a'},
    @{Pid=DEEP_PID;Source='refine_completed_parent_pending.py';Output='--output n25-B16-deep5'}
)
$taskCaptured = @()
foreach ($taskSpec in $taskSpecs) {
    $taskProcess = Get-Process -Id $taskSpec.Pid
    $taskHandle = $taskProcess.Handle
    $taskStart = $taskProcess.StartTime.ToUniversalTime().ToFileTimeUtc()
    $taskInfo = Get-CimInstance Win32_Process -Filter ('ProcessId = '+$taskSpec.Pid)
    if ($null -eq $taskInfo) { throw 'Existing process identity unavailable' }
    if ([decimal]::Floor(([decimal]$taskStart) / 10) -ne [decimal]::Floor(([decimal]$taskInfo.CreationDate.ToUniversalTime().ToFileTimeUtc()) / 10)) {
        throw 'Existing PID creation identity differs'
    }
    if ($taskInfo.Name -ne 'python.exe') { throw 'Wrong existing process image' }
    if (-not $taskInfo.CommandLine.Contains($taskSpec.Source)) { throw 'Wrong existing source' }
    if (-not $taskInfo.CommandLine.Contains($taskSpec.Output)) { throw 'Wrong existing output' }
    $taskCaptured += @{Process=$taskProcess;Pid=$taskSpec.Pid;Start=$taskStart;Command=$taskInfo.CommandLine}
}
$taskResults = @()
foreach ($taskItem in $taskCaptured) {
    $taskItem.Process.WaitForExit()
    $taskItem.Process.Refresh()
    $taskResults += [PSCustomObject]@{
        OriginalPid=$taskItem.Pid
        OriginalCreationFileTimeIdentity=$taskItem.Start.ToString()
        OriginalCommandLine=$taskItem.Command
        ActualExitCode=$taskItem.Process.ExitCode
        OriginalCachedProcessHandleTerminalObserved=$taskItem.Process.HasExited
    }
}
ConvertTo-Json -InputObject $taskResults -Compress
""".replace("AUDIT_PID", str(auditpid)).replace("DEEP_PID", str(deeppid))
    result = subprocess.run(
        ["powershell.exe", "-NoProfile", "-NonInteractive", "-Command", script],
        check=True, capture_output=True, encoding="utf8",
        creationflags=subprocess.CREATE_NO_WINDOW)
    terminals = json.loads(result.stdout)
    assert {row["OriginalPid"] for row in terminals} == {auditpid, deeppid}
    publish(output / "EXISTING-TERMINALS.json", {
        "actual_observed_original_cached_handle_terminals": terminals,
        "source_sha256": sha(Path(__file__)),
    })
    assert all(row["OriginalCachedProcessHandleTerminalObserved"] and row["ActualExitCode"] == 0
               for row in terminals)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--audit-pid", type=int, required=True)
    ap.add_argument("--deep-pid", type=int, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    snapshotpath = ROOT / "n25-B16-all37624-complete-parent-pending-snapshot-20261005-v1.json"
    base = ROOT / "n25-B16-f1-a"
    controls = ROOT / "n25-mixed-parent-controls-v1/VERIFIED.json"
    auditpath = ROOT / "audit_n25_parent_mixed_supplements.py"
    invoker = ROOT / "invoke_n25_mixed_manifest.py"
    control = read(controls)
    assert control["verified"] and control["audit_source_sha256"] == sha(auditpath)
    frozen = {str(path): sha(path) for path in (
        Path(__file__), snapshotpath, controls, auditpath, invoker,
        ROOT / "audit_library_parent_fillings.py", ROOT / "refine_completed_parent_pending.py",
        ROOT / "audit_n25_attaining_parent_transport.py",
        ROOT / "n25-B16-p115569-nonstrict1/VERIFIED.json",
        ROOT / "n25-B16-single-candidate-collar-closure-20261005-v1.json")}
    output.mkdir()
    publish(output / "PIPELINE-INPUT-BINDINGS.json", {
        "N": 25, "B": 16, "existing_audit_pid": args.audit_pid, "existing_deep_pid": args.deep_pid,
        "frozen_files": frozen, "original_existing_jobs_not_restarted": True,
        "actual_existing_successful_terminals_required_before_merge": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("B16 final successor observes actual existing audit/deep handles;",
          "no restart and no premature parent payment", flush=True)
    wait_existing(args.audit_pid, args.deep_pid, output)
    accepted = read(base / "VERIFIED.json")
    assert accepted["verified"] and accepted["source_sha256"] == sha(ROOT / "audit_library_parent_fillings.py")
    assert (accepted["N"], accepted["B"], accepted["complete_parent_weak_graphs"]) == (25, 16, 120782)
    assert accepted["remaining_weak_graphs"] == 234
    stage = ROOT / "n25-B16-all29556-library-parent-gapped-fillings-solo-v1"
    additions, parentids = [], set()
    examples = [(91, 47808), *[(327, pid) for pid in (86819, 86822, 86828, 86837, 86927)],
                *[(330, pid) for pid in (87535, 87536, 87538, 87541)]]
    for batch, pid in examples:
        additions.append([pid, str(stage / f"batch-{batch:06}/parent-{pid:07}"),
                          str(ROOT / f"n25-B16-p{pid}-f511-proposal-v1.json"),
                          str(ROOT / f"n25-B16-p{pid}-f511-exact-v1.json")])
        assert pid not in parentids
        parentids.add(pid)
    for name in ("n25-B16-deep1", "n25-B16-deep2", "n25-B16-deep3", "n25-B16-deep4", "n25-B16-deep5"):
        summarypath = ROOT / name / "SUMMARY.json"
        summary = read(summarypath)
        assert summary["source_sha256"] == sha(ROOT / "refine_completed_parent_pending.py")
        assert summary["all_independent_child_terminals_actually_observed"]
        assert summary["whole_families_strictly_closed"] == summary["selected_families"]
        for row in summary["outcomes"]:
            pid = row["parent_index"]
            assert row["whole_family_strictly_closed"] and pid not in parentids
            assert sha(row["proof_path"]) == row["proof_sha256"]
            assert sha(row["exact_path"]) == row["exact_sha256"]
            additions.append([pid, row["family"], row["proof_path"], row["exact_path"]])
            parentids.add(pid)
        frozen[str(summarypath)] = sha(summarypath)
    assert len(additions) == len(parentids) == 233 and 115569 not in parentids
    for path, digest in frozen.items():
        assert sha(path) == digest
    manifestpath = output / "MIXED-ARGUMENTS.json"
    publish(manifestpath, {
        "schema": "N25-mixed-parent-frozen-argument-manifest-v1",
        "snapshot": str(snapshotpath), "base": str(base), "controls": str(controls),
        "output": str(output / "ACCEPTED"), "additions": additions,
        "nonstrict": [[str(ROOT / "n25-B16-p115569-nonstrict1/VERIFIED.json"),
                      str(ROOT / "n25-B16-single-candidate-collar-closure-20261005-v1.json")]],
        "audit_source_sha256": sha(auditpath), "source_sha256": sha(Path(__file__)),
    })
    with (output / "MIXED-STDOUT.log").open("xb") as stdout, \
            (output / "MIXED-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen(
            [sys.executable, "-u", str(invoker), "--manifest", str(manifestpath)],
            cwd=str(ROOT), stdout=stdout, stderr=stderr,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / "MIXED-TERMINAL.json", {
        "actual_exit_code": code, "child_pid": process.pid,
        "independent_process_terminal_observed": True, "audit_source_sha256": sha(auditpath),
        "argument_manifest_sha256": sha(manifestpath),
    })
    assert code == 0
    finalpath = output / "ACCEPTED/VERIFIED.json"
    result = read(finalpath)
    assert result["verified"] and result["remaining_weak_graphs"] == 0
    assert result["complete_necessary_family_lower_payments_closed"]
    for path, digest in frozen.items():
        assert sha(path) == digest
    publish(output / "PIPELINE-COMPLETED.json", {
        "N": 25, "B": 16, "complete_parent_weak_graphs": 120782,
        "remaining_weak_graphs": 0, "actual_existing_and_new_audit_terminals_observed": True,
        "final_parent_report_sha256": sha(finalpath), "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("B16 all120782 necessary parent lower payments closed; not N25 global", flush=True)


if __name__ == "__main__":
    main()
