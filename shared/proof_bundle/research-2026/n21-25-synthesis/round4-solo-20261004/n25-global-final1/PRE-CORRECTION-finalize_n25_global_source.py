"""Real B17-final terminal, complete premise closure, independent N25 adoption."""
from pathlib import Path
from copy import deepcopy
import argparse
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from bind_n25_all_final_prerequisites import (
    interface_gate, final_gate, verify_ledger, SOURCEPATH, COREPATH, BUDGETPATH,
    DOCUMENT, FINALPATHS, TOTALS)

assert __debug__
BINDER = ROOT / "bind_n25_all_final_prerequisites.py"


def premise_gate(binding, source, core, budget, finals):
    interface_gate(source, core, budget)
    assert binding["verified"] and binding["N"] == 25
    assert binding["schema"] == "N25-four-whole-source-family-same-radical-root-current-premise-byte-closure-v1"
    assert binding["all_required_families"] == [14, 15, 16, 17]
    assert binding["complete_necessary_residual_weak_graphs"] == 721329
    for flag in (
        "all_four_actual_full_payment_ledgers_independently_sequentially_scanned",
        "all_parent_final_lower_chains_zero",
        "actual_B17_original_and_final_adopter_successful_terminals_checked",
        "all_actual_nonzero_strict_library_pruning_bound_to_own_complete_source_interface",
        "own_exact_radical_upper_fresh_local_and_real_complete_nonstrict_core_bound",
        "all_current_content_bindings_checked",
        "old_mathematics_honestly_reused_not_new_all_old_tree_replays",
        "written_math_not_claimed_machine_proved_by_content_checks"):
        assert binding[flag]
    assert not binding["mismatches"]
    assert binding["source_sha256"] == sha(BINDER)
    assert binding["four_actual_source_interface_sha256"] == sha(SOURCEPATH)
    assert binding["same_root_upper_local_real_full_core_interface_sha256"] == sha(COREPATH)
    assert binding["own_family_budget_sha256"] == sha(BUDGETPATH)
    assert binding["global_source_manuscript_sha256"] == sha(DOCUMENT)
    assert len(binding["family_partitions"]) == 4
    assert set(finals) == {14, 15, 16, 17}
    for row, B in zip(binding["family_partitions"], range(14, 18), strict=True):
        assert (row["B"], row["complete_necessary_parents"], row["pending"]) == (B, TOTALS[B], 0)
        assert row["final_path"] == str(FINALPATHS[B])
        assert row["final_sha256"] == sha(FINALPATHS[B])
        final_gate(B, finals[B])
    assert not binding["global_optimality_proved"]


def control_gate(binding, source, core, budget, finals):
    premise_gate(binding, source, core, budget, finals)
    refused = []
    cases = [
        ("binding", "N", 24), ("binding", "all_required_families", [14, 15, 16]),
        ("binding", "complete_necessary_residual_weak_graphs", 721328),
        ("binding", "all_parent_final_lower_chains_zero", False),
        ("binding", "all_four_actual_full_payment_ledgers_independently_sequentially_scanned", False),
        ("binding", "actual_B17_original_and_final_adopter_successful_terminals_checked", False),
        ("binding", "all_actual_nonzero_strict_library_pruning_bound_to_own_complete_source_interface", False),
        ("binding", "own_exact_radical_upper_fresh_local_and_real_complete_nonstrict_core_bound", False),
        ("binding", "mismatches", ["bad-proof-tree"]),
        ("binding", "old_mathematics_honestly_reused_not_new_all_old_tree_replays", False),
        ("binding", "written_math_not_claimed_machine_proved_by_content_checks", False),
        ("binding", "global_optimality_proved", True),
        ("source", "N", 24),
        ("source", "necessary_boundary_internal_families", [[14, 11], [15, 10], [16, 9]]),
        ("source", "actual_223_loaded_strict_library_trees_fresh_exactly_mathematically_reaccepted", False),
        ("source", "all_selected_actual_nonzero_pruning_uses_fully_validated_injection_on_each_positive_return", False),
        ("source", "correct_B14_origin_later_payment_and_B15_degree_upper_and_B15_B16_candidate_cache_scopes", False),
        ("core", "N", 23), ("core", "exact_radius_squared_Qsqrt2", ["1", "-1/3"]),
        ("core", "specified_core_lower_nonstrict_R_not_strict_U_and_not_all_competing_graphs", False),
        ("core", "actual_full91_family_and_unique_full_core_all_center_anchor_and_face_maps_rechecked", False),
        ("core", "specified311883_node_entire_core_math_honestly_reused_unchanged_not_claimed_new_replay", False),
        ("budget", "necessary_boundary_internal_families", [[14, 11], [15, 10], [17, 8]]),
    ]
    for label, key, value in cases:
        wrong = dict(binding=binding, source=source, core=core, budget=budget, finals=finals)
        wrong[label] = dict(wrong[label])
        wrong[label][key] = value
        try:
            premise_gate(**wrong)
        except (AssertionError, KeyError):
            refused.append(label+"-"+key)
        else:
            raise AssertionError("incorrect final global source premise accepted: "+label+"-"+key)
    for B, key, value in (
        (14, "pending_weak_graphs", 1), (15, "remaining_weak_graphs", 1),
        (16, "attaining_parent_not_recast_as_a_strict_upper_radius_exclusion", False),
        (17, "remaining_weak_graphs", 1),
        (17, "only_actual_accepted_parent_pending_indices_paid", False),
        (17, "additional_strict_complete_families", 38)):
        wrong = dict(finals)
        wrong[B] = dict(finals[B])
        wrong[B][key] = value
        try:
            premise_gate(binding, source, core, budget, wrong)
        except (AssertionError, KeyError):
            refused.append(f"final{B}-"+key)
        else:
            raise AssertionError("incorrect final actual parent scope accepted")
    assert len(refused) == 29
    return refused


def audit(bindingdir, inputs, output):
    assert not output.exists()
    before = read(inputs)
    for path, digest in before["new_global_entry_frozen_files"].items():
        assert sha(path) == digest
    original = read(inputs.parent / "ORIGINAL-B17-FINAL-TERMINAL.json")
    assert original["OriginalCachedProcessHandleTerminalObserved"] and original["ActualExitCode"] == 0
    terminal = read(inputs.parent / "BINDING-TERMINAL.json")
    assert terminal["actual_child_terminal_observed"] and terminal["actual_exit_code"] == 0
    bindingpath = bindingdir / "VERIFIED.json"
    assert sha(bindingpath) == before["binding_report_sha256"]
    binding, source, core, budget = map(read, (bindingpath, SOURCEPATH, COREPATH, BUDGETPATH))
    finals = {B: read(path) for B, path in FINALPATHS.items()}
    refusals = control_gate(binding, source, core, budget, finals)
    for row in binding["family_partitions"]:
        ledger, pending = Path(row["payment_ledger_path"]), Path(row["pending_ledger_path"])
        assert sha(ledger) == row["payment_ledger_sha256"] and sha(pending) == row["pending_ledger_sha256"]
        actual = verify_ledger(row["B"], finals[row["B"]], ledger, pending)
        assert actual == row["actual_payment_kinds"]
    ledger = bindingdir / "CURRENT-INPUTS.jsonl"
    assert sha(ledger) == binding["current_input_ledger_sha256"]
    output.mkdir()
    count, previous, differences = 0, None, []
    with ledger.open(encoding="ascii") as stream, \
            (output / "FROZEN-INPUTS.jsonl").open("x", encoding="ascii") as target:
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert set(row) == {"path", "sha256"}
            path = Path(row["path"]).resolve()
            assert str(path) == row["path"] and path.is_absolute() and (
                path.is_relative_to(ROOT.parents[4]) or
                path.is_relative_to(ROOT.parents[4].parent / "dependencies"))
            assert previous is None or previous < row["path"]
            previous = row["path"]
            if sha(path) != row["sha256"]:
                differences.append(row["path"])
            target.write(line)
            count += 1
            if count % 5000 == 0:
                print("N25 final independent complete source-proof content audit", count, "/",
                      binding["current_files_and_whole_archives_checked"],
                      "differences", len(differences), flush=True)
    assert count == binding["current_files_and_whole_archives_checked"] and not differences, differences
    assert sha(ledger) == binding["current_input_ledger_sha256"]
    assert sha(bindingpath) == before["binding_report_sha256"]
    for path, digest in before["new_global_entry_frozen_files"].items():
        assert sha(path) == digest
    upperpath = ROOT / "n25-own-exact-upper-fresh-v1/VERIFIED.json"
    upper = read(upperpath)
    assert upper["verified"] and core["fresh_upper_report_sha256"] == sha(upperpath)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "GLOBAL-SOURCE-ACCEPTED.json", {
        "verified": True, "schema": "N25-arbitrary-unit-closed-disk-cover-global-computer-assisted-source-proof-v1",
        "N": 25, "theorem": "r_D(25)=1/(sqrt(6)+sqrt(3))",
        "exact_radius": "1/(sqrt(6)+sqrt(3))", "exact_radius_squared_Qsqrt2": ["1", "-2/3"],
        "strict_radius_interval": upper["r_strict_interval"],
        "arbitrary_plane_centers_repetitions_fewer_disks_and_degeneracies_allowed": True,
        "no_symmetry_or_fixed_contact_graph_assumed": True,
        "same_exact_radical_entire25_disk_upper_and_all_necessary_family_lower_proofs": True,
        "required_boundary_families": [14, 15, 16, 17],
        "complete_necessary_residual_weak_graph_counts": list(TOTALS.values()),
        "complete_necessary_residual_weak_graphs": 721329, "all_pending_families": 0,
        "family_partitions": binding["family_partitions"],
        "all_actual_nonzero_strict_library_pruning_proofs_and_positive_injection_checks_bound": True,
        "actual223_selected_strict_library_trees_freshly_reaccepted_in_own_source_interface": True,
        "actual_parent115569_full91_family_90strict_and1_same_root_core_bound": True,
        "actual_attaining_parent_not_recast_as_strict_upper_exclusion_or_all_attainers_classification": True,
        "full288_variable_KKT_root_not_falsely_claimed_isolated": True,
        "written_cover_peeling_degree_pruning_and_local_quadratic_mathematics_reviewed_source_premises": True,
        "written_math_not_claimed_machine_proved_by_content_check": True,
        "all_old_exact_mathematics_honestly_reused_not_new_full_all_old_tree_replays": True,
        "current_files_and_whole_archives_independently_rechecked": count,
        "all_actual_four_final_parent_payment_ledgers_independently_sequentially_rescanned": True,
        "source_document_sha256": sha(DOCUMENT), "all_prerequisites_binding_sha256": sha(bindingpath),
        "four_actual_source_interface_sha256": sha(SOURCEPATH),
        "same_exact_root_upper_local_real_full_core_interface_sha256": sha(COREPATH),
        "frozen_input_ledger_sha256": sha(output / "FROZEN-INPUTS.jsonl"),
        "new_global_entry_frozen_files": before["new_global_entry_frozen_files"],
        "negative_global_scope_controls_rejected": refusals, "source_sha256": sha(Path(__file__)),
        "original_B17_final_and_binding_actual_successful_terminals_observed": True,
        "not_Lean_Coq_formalization_not_third_party_peer_review_not_all_attaining_configurations_classified": True,
        "global_source_proof_closed": True, "global_optimality_proved": True})
    print("N25 arbitrary-cover global computer-assisted SOURCE proof independent acceptance complete;",
          "old mathematics honestly reused; not formalization or third-party review", flush=True)


def wait_original(pid, output):
    assert os.name == "nt" and type(pid) is int and pid > 0
    script = r"""
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
$ErrorActionPreference = 'Stop'
$taskProcess = Get-Process -Id TASK_PID
$taskHandle = $taskProcess.Handle
$taskStart = $taskProcess.StartTime.ToUniversalTime().ToFileTimeUtc()
$taskInfo = Get-CimInstance Win32_Process -Filter 'ProcessId = TASK_PID'
if ($null -eq $taskInfo) { throw 'Original B17 final process identity unavailable' }
if ([decimal]::Floor(([decimal]$taskStart) / 10) -ne [decimal]::Floor(([decimal]$taskInfo.CreationDate.ToUniversalTime().ToFileTimeUtc()) / 10)) {
    throw 'Original PID creation identity differs'
}
if ($taskInfo.Name -ne 'python.exe') { throw 'Wrong original B17 final image' }
if (-not $taskInfo.CommandLine.Contains('run_n25_B17_final_after_original.py')) { throw 'Wrong original B17 final source' }
if (-not $taskInfo.CommandLine.Contains('n25-B17-final1')) { throw 'Wrong original B17 final output' }
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
    publish(output / "ORIGINAL-B17-FINAL-TERMINAL.json", terminal)
    assert terminal["OriginalPid"] == pid
    assert terminal["OriginalCachedProcessHandleTerminalObserved"] and terminal["ActualExitCode"] == 0


def run_child(command, label, output):
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
    ap.add_argument("--audit-only", action="store_true")
    ap.add_argument("--binding", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--inputs", type=Path)
    ap.add_argument("--wait-final-pid", type=int)
    args = ap.parse_args()
    binding, output = args.binding.resolve(), args.output.resolve()
    assert binding.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    if args.audit_only:
        assert args.inputs is not None
        audit(binding, args.inputs.resolve(), output)
        return
    assert args.wait_final_pid is not None and not binding.exists()
    frozen = {str(path): sha(path) for path in (
        Path(__file__), BINDER, DOCUMENT, SOURCEPATH, COREPATH, BUDGETPATH,
        *[FINALPATHS[B] for B in (14, 15, 16)],
        ROOT / "run_n25_B17_final_after_original.py", ROOT / "invoke_n25_B17_supplement_manifest.py",
        ROOT / "audit_n25_parent_direct_supplements.py",
        ROOT / "NECESSARY-OUTER-COLLAR-ARBITRARY-COVER-INDUCTION-v1.md",
        ROOT / "N23-N24-COVER-AND-FULL-PEEL-INDUCTION-v1.md")}
    output.mkdir()
    publish(output / "LAUNCH-INPUTS.json", {
        "N": 25, "actual_original_B17_final_pid": args.wait_final_pid,
        "new_global_entry_frozen_files": frozen,
        "no_restart_and_no_source_binding_or_global_adoption_before_actual_complete_B17_zero": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})
    print("N25 global successor caches actual original B17-final handle; complete four-family binding",
          "and independent global audit only after its actual terminal and formal zero", flush=True)
    wait_original(args.wait_final_pid, output)
    for path, digest in frozen.items():
        assert sha(path) == digest
    final_gate(17, read(FINALPATHS[17]))
    frozen[str(FINALPATHS[17])] = sha(FINALPATHS[17])
    run_child([sys.executable, "-u", BINDER, "--output", binding], "BINDING", output)
    for name in ("ORIGINAL-B17-FINAL-TERMINAL.json", "BINDING-TERMINAL.json"):
        frozen[str(output / name)] = sha(output / name)
    inputspath = output / "INPUT-BINDINGS.json"
    publish(inputspath, {
        "N": 25, "new_global_entry_frozen_files": frozen,
        "binding_report_sha256": sha(binding / "VERIFIED.json"),
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})
    run_child([sys.executable, "-u", Path(__file__), "--audit-only", "--binding", binding,
               "--inputs", inputspath, "--output", output / "ACCEPTED"], "FINAL-AUDIT", output)
    for path, digest in frozen.items():
        assert sha(path) == digest
    acceptedpath = output / "ACCEPTED/GLOBAL-SOURCE-ACCEPTED.json"
    accepted = read(acceptedpath)
    assert accepted["verified"] and accepted["global_source_proof_closed"]
    publish(output / "PIPELINE-COMPLETED.json", {
        "N": 25, "actual_original_B17_final_binding_and_independent_global_audit_successfully_observed": True,
        "final_global_source_acceptance_sha256": sha(acceptedpath), "source_sha256": sha(Path(__file__)),
        "global_source_proof_closed": True,
        "scope": "qualified computer-assisted SOURCE proof; not formalization or third-party review"})


if __name__ == "__main__":
    main()
