"""Keep the actual original B17 handle, then adopt its real formal residuals.

No restart, prefix adoption, or edited old proof. New late residuals may be
deepened once in a unique stage; unresolved cases remain explicitly unpaid.
"""
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish

assert __debug__
STAGE = ROOT / "n25-B17-f1"
SNAPSHOT = ROOT / "n25-B17-full-root-to-entire-residual-fillings-pipeline-solo-v1/ALL-PENDING-SNAPSHOT.json"
CONTROLS = ROOT / "n25-b16-b17-direct-supplement-controls-v1/VERIFIED.json"
BASE = STAGE / "COMPLETE-PAYMENT-AUDIT"


def ended_supplements():
    snapshot, inputs = read(SNAPSHOT), read(STAGE / "INPUT-BINDINGS.json")
    assert (snapshot["N"], snapshot["B"], snapshot["selected_pending_graphs"]) == (25, 17, 66857)
    assert (inputs["N"], inputs["B"], inputs["worker_batch_size"]) == (25, 17, 128)
    assert inputs["snapshot_sha256"] == sha(SNAPSHOT)
    positions = {row["parent_index"]: i for i, row in enumerate(snapshot["graphs"])}
    assert len(positions) == 66857
    ready, frozen = {}, {}

    def add(pid, family, proof, exact, expected_proof=None, expected_exact=None):
        family, proof, exact = map(lambda path: Path(path).resolve(), (family, proof, exact))
        assert pid in positions and pid not in ready
        assert family == STAGE / f"batch-{positions[pid]//128:06}/parent-{pid:07}"
        assert proof.is_relative_to(ROOT) and exact.is_relative_to(ROOT)
        accepted, payload = read(exact), read(proof)
        assert (accepted["N"], accepted["B"]) == (payload["N"], payload["B"]) == (25, 17)
        assert accepted["verified"] and accepted["all_full_simple_disk_completions_strictly_paid"]
        assert accepted["pending_complete_leaves"] == accepted["unsearched_frontier_nodes"] == 0
        assert accepted["source_sha256"] == sha(ROOT / "replay_refined_linked_leaves.py")
        assert payload["source_collar_sha256"] == sha(family / "INPUT-COLLAR.json")
        assert payload["original_proposal_sha256"] == sha(family / "PROPOSAL.json")
        assert payload["original_exact_replay_sha256"] == sha(family / "EXACT.json")
        for path, digest in ((proof, expected_proof), (exact, expected_exact)):
            actual = sha(path)
            assert digest is None or digest == actual
            frozen[str(path)] = actual
        for name in ("INPUT-COLLAR.json", "PROPOSAL.json", "EXACT.json"):
            path = family / name
            frozen[str(path)] = sha(path)
        ready[pid] = {"parent_index": pid, "family": str(family),
                      "proof_path": str(proof), "exact_path": str(exact)}

    for pid in (5669, 5679, 5778, 29605, 29608, 29619, 29749):
        family = STAGE / f"batch-{positions[pid]//128:06}/parent-{pid:07}"
        add(pid, family, ROOT / f"n25-B17-p{pid}-f511-proposal-v1.json",
            ROOT / f"n25-B17-p{pid}-f511-exact-v1.json")
    for name in ("n25-B17-deep1", "n25-B17-deep2", "n25-B17-deep3"):
        directory = ROOT / name
        summarypath = directory / "SUMMARY.json"
        summary = read(summarypath)
        assert (summary["N"], summary["B"]) == (25, 17)
        assert summary["source_sha256"] == sha(ROOT / "refine_completed_parent_pending.py")
        assert summary["all_independent_child_terminals_actually_observed"]
        assert summary["whole_families_strictly_closed"] == summary["selected_families"]
        frozen[str(summarypath)] = sha(summarypath)
        for row in summary["outcomes"]:
            assert row["whole_family_strictly_closed"]
            for label in ("PROPOSE", "REPLAY"):
                terminalpath = directory / f"p{row['parent_index']}-{label}-TERMINAL.json"
                terminal = read(terminalpath)
                assert terminal["actual_exit_code"] == 0 and terminal["independent_process_terminal_observed"]
                frozen[str(terminalpath)] = sha(terminalpath)
            add(row["parent_index"], row["family"], row["proof_path"], row["exact_path"],
                row["proof_sha256"], row["exact_sha256"])
    assert len(ready) == 39
    return ready, frozen


def wait_original(pid, output):
    assert os.name == "nt" and type(pid) is int and pid > 0
    script = r"""
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
$ErrorActionPreference = 'Stop'
$taskProcess = Get-Process -Id TASK_PID
$taskHandle = $taskProcess.Handle
$taskStart = $taskProcess.StartTime.ToUniversalTime().ToFileTimeUtc()
$taskInfo = Get-CimInstance Win32_Process -Filter 'ProcessId = TASK_PID'
if ($null -eq $taskInfo) { throw 'Original B17 process identity unavailable' }
if ([decimal]::Floor(([decimal]$taskStart) / 10) -ne [decimal]::Floor(([decimal]$taskInfo.CreationDate.ToUniversalTime().ToFileTimeUtc()) / 10)) {
    throw 'Original PID creation identity differs'
}
if ($taskInfo.Name -ne 'python.exe') { throw 'Wrong original B17 image' }
if (-not $taskInfo.CommandLine.Contains('pay_complete_origin_pending.py')) { throw 'Wrong original B17 source' }
if (-not $taskInfo.CommandLine.Contains('--output n25-B17-f1')) { throw 'Wrong original B17 output' }
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
    result = subprocess.run(["powershell.exe", "-NoProfile", "-NonInteractive", "-Command", script],
                            capture_output=True, encoding="utf8", check=True,
                            creationflags=subprocess.CREATE_NO_WINDOW)
    terminal = json.loads(result.stdout)
    publish(output / "ORIGINAL-B17-TERMINAL.json", terminal)
    assert terminal["OriginalPid"] == pid
    assert terminal["OriginalCachedProcessHandleTerminalObserved"] and terminal["ActualExitCode"] == 0


def child(command, label, output):
    with (output / (label+"-STDOUT.log")).open("xb") as stdout, \
            (output / (label+"-STDERR.log")).open("xb") as stderr:
        process = subprocess.Popen(list(map(str, command)), cwd=str(ROOT), stdout=stdout, stderr=stderr,
                                   creationflags=subprocess.CREATE_NO_WINDOW)
        code = process.wait()
    publish(output / (label+"-TERMINAL.json"), {
        "pid": process.pid, "actual_exit_code": code, "actual_child_terminal_observed": True,
        "source_sha256": sha(Path(__file__))})
    assert code == 0, (label, code)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--wait-pid", type=int, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    ready, frozen = ended_supplements()
    controls = read(CONTROLS)
    assert controls["verified"] and controls["audit_source_sha256"] == sha(ROOT / "audit_n25_parent_direct_supplements.py")
    for path in (
        Path(__file__), SNAPSHOT, STAGE / "INPUT-BINDINGS.json", CONTROLS,
        ROOT / "audit_n25_parent_direct_supplements.py", ROOT / "invoke_n25_B17_supplement_manifest.py",
        ROOT / "pay_complete_origin_pending.py", ROOT / "audit_complete_origin_fillings.py",
        ROOT / "refine_completed_parent_pending.py"):
        frozen[str(path)] = sha(path)
    output.mkdir()
    publish(output / "LAUNCH-INPUTS.json", {
        "N": 25, "B": 17, "original_B17_pid": args.wait_pid,
        "ready39_from_real_ended_families_not_assumed_final_residual_count": [ready[p] for p in sorted(ready)],
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})
    print("B17 successor caches actual original complete scheduler/audit handle; no restart;",
          "39 ended strict supplements adopted only against its genuine final residual", flush=True)
    wait_original(args.wait_pid, output)
    for path, digest in frozen.items():
        assert sha(path) == digest
    base = read(BASE / "VERIFIED.json")
    assert base["verified"] and (base["N"], base["B"], base["parent_weak_graphs"]) == (25, 17, 289140)
    assert base["source_sha256"] == sha(ROOT / "audit_complete_origin_fillings.py")
    assert base["all_complete_parent_rows_partitioned_once"]
    assert base["all_positive_weak_force_and_filling_trees_freshly_replayed"]
    terminal = read(STAGE / "FULL-PARENT-AUDIT-TERMINAL.json")
    assert terminal["actual_exit_code"] == 0
    assert sha(BASE / "PENDING.jsonl") == base["pending_sha256"]
    pending = {}
    with (BASE / "PENDING.jsonl").open(encoding="ascii") as stream:
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            pid = row["parent_index"]
            assert type(pid) is int and pid not in pending
            pending[pid] = row
    assert len(pending) == base["remaining_weak_graphs"] and set(ready) <= set(pending)
    late = set(pending)-set(ready)
    if late:
        deep = output / "LATE-PENDING-DEEP"
        child([sys.executable, "-u", ROOT / "refine_completed_parent_pending.py",
               "--stage", STAGE, "--output", deep, "--force-limit", "511",
               "--skip-parent", *map(str, sorted(ready))], "LATE-DEEP", output)
        summary = read(deep / "SUMMARY.json")
        assert {row["parent_index"] for row in summary["outcomes"]} == late
        assert summary["all_independent_child_terminals_actually_observed"]
        frozen[str(deep / "SUMMARY.json")] = sha(deep / "SUMMARY.json")
        for row in summary["outcomes"]:
            if row["whole_family_strictly_closed"]:
                assert sha(row["proof_path"]) == row["proof_sha256"]
                assert sha(row["exact_path"]) == row["exact_sha256"]
                ready[row["parent_index"]] = {key: row[key] for key in (
                    "parent_index", "family", "proof_path", "exact_path")}
                frozen[row["proof_path"]] = row["proof_sha256"]
                frozen[row["exact_path"]] = row["exact_sha256"]
    manifestpath = output / "FORMAL-SUPPLEMENTS.json"
    frozen[str(BASE / "VERIFIED.json")] = sha(BASE / "VERIFIED.json")
    publish(manifestpath, {
        "N": 25, "B": 17, "snapshot": str(SNAPSHOT), "base": str(BASE),
        "controls": str(CONTROLS), "output": str(output / "ACCEPTED"),
        "additions": [ready[p] for p in sorted(ready)],
        "actual_formal_pending_count": len(pending), "late_families": sorted(late),
        "adopter_source_sha256": sha(ROOT / "audit_n25_parent_direct_supplements.py"),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})
    child([sys.executable, "-u", ROOT / "invoke_n25_B17_supplement_manifest.py",
           "--manifest", manifestpath], "FINAL-PARENT-AUDIT", output)
    reportpath = output / "ACCEPTED/VERIFIED.json"
    report = read(reportpath)
    assert report["verified"] and (report["N"], report["B"], report["complete_parent_weak_graphs"]) == (25, 17, 289140)
    assert report["additional_strict_complete_families"] == len(ready)
    for path, digest in frozen.items():
        assert sha(path) == digest
    publish(output / "PIPELINE-COMPLETED.json", {
        "N": 25, "B": 17, "actual_original_and_independent_final_adopter_terminals_observed": True,
        "complete_parent_weak_graphs": 289140, "remaining_weak_graphs": report["remaining_weak_graphs"],
        "whole_necessary_B17_family_lower_paid": report["remaining_weak_graphs"] == 0,
        "ready39_not_substituted_for_real_formal_pending_count": True,
        "final_parent_report_sha256": sha(reportpath), "source_sha256": sha(Path(__file__)),
        "source_cover_same_root_upper_and_global_freeze_still_required": True,
        "global_optimality_proved": False})


if __name__ == "__main__":
    main()
