"""Observe the original last parent terminal, bind, and independently audit N24.

This adopts reviewed written source mathematics and previously accepted exact
computations. Hash checks are not a formal proof or a fresh replay of old trees.
"""
from pathlib import Path
from copy import deepcopy
import argparse
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from bind_n24_all_final_prerequisites import final_gate, EXPECTED, SOURCEPATH
from n24_actual_core_transport import own_core_gate, COREPATH, SYSTEMPATH

assert __debug__
DOCUMENT = ROOT / "N24-GLOBAL-SOURCE-PROOF-v1.md"
BIND_SOURCE = ROOT / "bind_n24_all_final_prerequisites.py"
FINAL15 = ROOT / "n24-B15-final1/VERIFIED.json"


def premise_gate(binding, source, core, mixed):
    assert binding["verified"]
    assert binding["schema"] == "N24-four-whole-necessary-family-same-root-global-premise-current-byte-closure-v1"
    assert binding["N"] == 24 and binding["all_required_families"] == [13, 14, 15, 16]
    assert binding["all_complete_sources_and_final_parent_lower_chains_zero"]
    assert binding["total_necessary_weak_graphs"] == 129178
    assert binding["all_current_content_bindings_checked"] and not binding["mismatches"]
    assert binding["all_real_own_core_full_leaves_rod_transport_and_nonstrict_status_bound"]
    assert binding["old_mathematics_honestly_reused_not_new_complete_old_tree_replays"]
    assert binding["written_math_not_claimed_machine_proved_by_hash_checks"]
    assert binding["source_sha256"] == sha(BIND_SOURCE)
    assert binding["source_interface_sha256"] == sha(SOURCEPATH)
    assert binding["same_root_proof_sha256"] == sha(COREPATH)
    assert binding["system_sha256"] == sha(SYSTEMPATH)
    assert binding["global_source_manuscript_sha256"] == sha(DOCUMENT)
    partitions = binding["family_partitions"]
    assert len(partitions) == 4
    for row, B in zip(partitions, range(13, 17), strict=True):
        total, weak, filling, refined, nonstrict = EXPECTED[B]
        assert (row["B"], row["total"], row["strict_weak"],
                row["strict_complete_first"], row["strict_complete_final"],
                row["own_nonstrict_mixed_complete"], row["pending"]) == (
                    B, total, weak, filling, refined, nonstrict, 0)
        assert weak+filling+refined+nonstrict == total
    assert source["verified"] and source["N"] == 24
    assert source["schema"] == "N24-reviewed-arbitrary-cover-collar-induction-bound-to-four-actual-full-sources-v1"
    assert source["necessary_boundary_internal_families"] == [[13, 11], [14, 10], [15, 9], [16, 8]]
    assert source["complete_necessary_weak_graph_counts"] == [4202, 10812, 31348, 82816]
    assert source["total_necessary_weak_graphs"] == 129178
    assert source["written_cover_full_peeling_and_pure_internal_omission_induction_reviewed_as_math_premises"]
    assert source["no_written_math_falsely_machine_proved_by_hash_or_small_reference_cases"]
    assert source["own_same_root_budget_upper_core_and_four_sources_bound"]
    assert source["source_sha256"] == sha(ROOT / "verify_n24_complete_source_interfaces.py")
    assert len(source["source_receipts"]) == 4
    for receipt, B in zip(source["source_receipts"], range(13, 17), strict=True):
        assert (receipt["N"], receipt["B"], receipt["necessary_weak_graphs"]) == (24, B, EXPECTED[B][0])
        assert receipt["real_full_root_unlimited_DFS_no_seed_no_force_or_sparse_payments"]
        assert receipt["own_actual_cover_origin_condition_not_standalone_weak_geometry"]
    assert core["verified"] and (core["N"], core["B"], core["core_centers"]) == (24, 15, 23)
    assert core["system_sha256"] == sha(SYSTEMPATH)
    for flag in (
        "exact_root_interval_and_same_root_entire_disk_upper_freshly_recomputed",
        "all_114_local_principal_minors_and_perturbation_gap_freshly_recomputed",
        "all_69215_core_angle_nodes_freshly_mathematically_replayed",
        "LOCAL_leaves_require_actual_fresh_root_and_isolation_not_historical_flags",
        "specified_core_lower_bound_nonstrict_same_root_not_strict_upper_exclusion"):
        assert core[flag]
    assert mixed["verified"] and (mixed["N"], mixed["B"]) == (24, 15)
    assert mixed["remaining_pending_families"] == 0
    assert mixed["new_own_strict_and_same_root_core_complete_families"] == 1
    assert mixed["full_parent_disjoint_partition_complete"]
    assert mixed["all_core_leaf_center_anchor_face_and_witness_rods_bound_to_own_N24_theorem"]
    assert mixed["core_remains_nonstrict_same_root_not_strict_upper_exclusion"]


def control_gate(binding, source, core, mixed):
    premise_gate(binding, source, core, mixed)
    refused = []
    cases = [
        ("binding", "verified", False), ("binding", "N", 25),
        ("binding", "all_required_families", [13, 14, 15]),
        ("binding", "total_necessary_weak_graphs", 129177),
        ("binding", "all_complete_sources_and_final_parent_lower_chains_zero", False),
        ("binding", "all_current_content_bindings_checked", False),
        ("binding", "mismatches", ["changed-evidence"]),
        ("binding", "all_real_own_core_full_leaves_rod_transport_and_nonstrict_status_bound", False),
        ("binding", "old_mathematics_honestly_reused_not_new_complete_old_tree_replays", False),
        ("source", "necessary_boundary_internal_families", [[13, 11], [14, 10], [15, 9]]),
        ("source", "complete_necessary_weak_graph_counts", [4202, 10812, 31348, 82815]),
        ("source", "written_cover_full_peeling_and_pure_internal_omission_induction_reviewed_as_math_premises", False),
        ("core", "N", 23), ("core", "core_centers", 24),
        ("core", "all_69215_core_angle_nodes_freshly_mathematically_replayed", False),
        ("mixed", "remaining_pending_families", 1),
        ("mixed", "new_own_strict_and_same_root_core_complete_families", 0),
        ("mixed", "core_remains_nonstrict_same_root_not_strict_upper_exclusion", False),
        ("mixed", "all_core_leaf_center_anchor_face_and_witness_rods_bound_to_own_N24_theorem", False),
    ]
    for label, key, value in cases:
        wrong = {"binding": binding, "source": source, "core": core, "mixed": mixed}
        wrong[label] = deepcopy(wrong[label])
        wrong[label][key] = value
        try:
            premise_gate(**wrong)
        except (AssertionError, KeyError):
            refused.append(label+"-"+key)
        else:
            raise AssertionError("incorrect final global source premise accepted: "+label+"-"+key)
    for field, value in (("pending", 1), ("strict_complete_final", 174),
                         ("own_nonstrict_mixed_complete", 0)):
        wrong = deepcopy(binding)
        wrong["family_partitions"][2 if field == "own_nonstrict_mixed_complete" else 3][field] = value
        try:
            premise_gate(wrong, source, core, mixed)
        except (AssertionError, KeyError):
            refused.append("partition-"+field)
        else:
            raise AssertionError("incorrect complete parent partition accepted")
    assert len(refused) == 22
    return refused


def audit(bindingdir, inputs, output):
    assert not output.exists()
    before = read(inputs)
    for path, digest in before["new_global_entry_frozen_files"].items():
        assert sha(path) == digest
    terminal = read(inputs.parent / "ORIGINAL-LAST-PARENT-TERMINAL.json")
    assert terminal["OriginalCachedProcessHandleTerminalObserved"] and terminal["ActualExitCode"] == 0
    bindingterminal = read(inputs.parent / "BINDING-TERMINAL.json")
    assert bindingterminal["actual_child_terminal_observed"] and bindingterminal["actual_exit_code"] == 0
    bindingpath = bindingdir / "VERIFIED.json"
    assert sha(bindingpath) == before["binding_report_sha256"]
    binding, source, core, mixed = read(bindingpath), read(SOURCEPATH), own_core_gate(), read(FINAL15)
    refusals = control_gate(binding, source, core, mixed)
    for row in binding["family_partitions"]:
        B = row["B"]
        sourcepath = ROOT / f"n24-B{B}-s1/ACCEPTED/SOURCE-ACCEPTED.json"
        lowerpath = ROOT / f"n24-B{B}-l1/ACCEPTED/VERIFIED.json"
        basepath = ROOT / f"n24-B{B}-f1/ACCEPTED/VERIFIED.json"
        finalpath = basepath if B == 13 else ROOT / f"n24-B{B}-final1/VERIFIED.json"
        assert str(finalpath) == row["final_path"]
        for path, key in ((sourcepath, "source_sha256"), (lowerpath, "lower_sha256"),
                          (basepath, "base_sha256"), (finalpath, "final_sha256")):
            assert sha(path) == row[key]
        final_gate(B, *map(read, (sourcepath, lowerpath, basepath, finalpath)))
    ledger = bindingdir / "CURRENT-INPUTS.jsonl"
    assert sha(ledger) == binding["current_input_ledger_sha256"]
    output.mkdir()
    count, previous, mismatches = 0, None, []
    with ledger.open(encoding="ascii") as stream, \
            (output / "FROZEN-INPUTS.jsonl").open("x", encoding="ascii") as target:
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert set(row) == {"path", "sha256", "origin"}
            path = Path(row["path"]).resolve()
            assert path.is_absolute() and (
                path.is_relative_to(ROOT.parents[4]) or
                path.is_relative_to(ROOT.parents[4].parent / "dependencies"))
            assert str(path) == row["path"]
            assert previous is None or previous < row["path"]
            previous = row["path"]
            if sha(path) != row["sha256"]:
                mismatches.append(row["path"])
            target.write(line)
            count += 1
            if count % 5000 == 0:
                print("N24 final independent entire source-proof content audit", count,
                      "/", binding["all_current_evidence_files_and_whole_archives"],
                      "differences", len(mismatches), flush=True)
    assert count == binding["all_current_evidence_files_and_whole_archives"] and not mismatches, mismatches
    assert sha(ledger) == binding["current_input_ledger_sha256"]
    assert sha(bindingpath) == before["binding_report_sha256"]
    for path, digest in before["new_global_entry_frozen_files"].items():
        assert sha(path) == digest
    root = read(COREPATH.parent / "root-verified.json")
    assert root["root_sha256"] == core["root_sha256"] and root["system_sha256"] == core["system_sha256"]
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "GLOBAL-SOURCE-ACCEPTED.json", {
        "verified": True, "schema": "N24-arbitrary-unit-closed-disk-cover-global-computer-assisted-source-proof-v1",
        "N": 24, "theorem": "r_D(24)=R",
        "exact_R": "positive square root of t=G114 in the isolated unique219-variable own root system; not a float",
        "root_sha256": core["root_sha256"], "system_sha256": core["system_sha256"],
        "strict_radius_interval": root["r_strict_interval"],
        "arbitrary_plane_centers_repetitions_fewer_disks_and_degeneracies_allowed": True,
        "no_symmetry_or_fixed_contact_graph_assumed": True,
        "same_exact_root_entire24_disk_upper_and_all_necessary_family_lower_proofs": True,
        "required_boundary_families": [13, 14, 15, 16],
        "complete_necessary_weak_graph_counts": [4202, 10812, 31348, 82816],
        "complete_necessary_weak_graphs": 129178, "family_partitions": binding["family_partitions"],
        "every_original_necessary_parent_paid_with_strict_or_actual_same_root_core": True,
        "all_pending_families": 0, "actual_nonstrict_mixed_parent_families": 1,
        "real_two_full_core_leaves_not_all_optimal_configurations_classification": True,
        "written_cover_peeling_and_local_quadratic_mathematics_reviewed_as_source_proof_premises": True,
        "written_math_not_claimed_machine_proved_by_hash_check": True,
        "all_old_exact_mathematics_honestly_reused_under_unchanged_full_content_bindings": True,
        "current_files_and_whole_archives_independently_rechecked": count,
        "old_E_paths_not_rewritten_or_claimed_present": True,
        "source_document_sha256": sha(DOCUMENT), "all_prerequisites_binding_sha256": sha(bindingpath),
        "four_full_source_interfaces_sha256": sha(SOURCEPATH),
        "own_full_core_transport_and_final_mixed_parent_sha256": sha(FINAL15),
        "same_exact_root_upper_local_and_entire_angle_proof_sha256": sha(COREPATH),
        "frozen_input_ledger_sha256": sha(output / "FROZEN-INPUTS.jsonl"),
        "new_global_entry_frozen_files": before["new_global_entry_frozen_files"],
        "negative_global_scope_controls_rejected": refusals, "source_sha256": sha(Path(__file__)),
        "original_last_parent_and_new_binding_actual_successful_terminals_observed": True,
        "not_Lean_Coq_formalization_not_third_party_peer_review_not_all_attaining_configurations_classified": True,
        "global_source_proof_closed": True, "global_optimality_proved": True})
    print("N24 arbitrary-cover global computer-assisted SOURCE proof independent acceptance complete;",
          "not formalization or third-party review; old math reused transparently", flush=True)


def wait_original(pid, output):
    assert os.name == "nt" and type(pid) is int and pid > 0
    script = r"""
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
$ErrorActionPreference = 'Stop'
$taskProcess = Get-Process -Id TASK_PID
$taskHandle = $taskProcess.Handle
$taskStart = $taskProcess.StartTime.ToUniversalTime().ToFileTimeUtc()
$taskInfo = Get-CimInstance Win32_Process -Filter 'ProcessId = TASK_PID'
if ($null -eq $taskInfo) { throw 'Original last parent process identity unavailable' }
if ([decimal]::Floor(([decimal]$taskStart) / 10) -ne [decimal]::Floor(([decimal]$taskInfo.CreationDate.ToUniversalTime().ToFileTimeUtc()) / 10)) {
    throw 'Original PID creation identity differs'
}
if ($taskInfo.Name -ne 'python.exe') { throw 'Wrong original parent image' }
if (-not $taskInfo.CommandLine.Contains('audit_small_order_parent_supplements.py')) { throw 'Wrong original parent source' }
if (-not $taskInfo.CommandLine.Contains('n24-B16-final1')) { throw 'Wrong original parent output' }
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
    publish(output / "ORIGINAL-LAST-PARENT-TERMINAL.json", terminal)
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
    ap.add_argument("--wait-parent-pid", type=int)
    args = ap.parse_args()
    binding, output = args.binding.resolve(), args.output.resolve()
    assert binding.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    if args.audit_only:
        assert args.inputs is not None
        audit(binding, args.inputs.resolve(), output)
        return
    assert args.wait_parent_pid is not None and not binding.exists()
    frozen = {str(path): sha(path) for path in (
        Path(__file__), BIND_SOURCE, DOCUMENT, SOURCEPATH, COREPATH, SYSTEMPATH, FINAL15,
        ROOT / "n24-B14-final1/VERIFIED.json",
        ROOT / "N23-N24-COVER-AND-FULL-PEEL-INDUCTION-v1.md",
        ROOT / "NECESSARY-OUTER-COLLAR-ARBITRARY-COVER-INDUCTION-v1.md",
        ROOT / "n24_actual_core_transport.py", ROOT / "audit_small_order_parent_supplements.py")}
    output.mkdir()
    publish(output / "LAUNCH-INPUTS.json", {
        "N": 24, "original_last_parent_pid": args.wait_parent_pid,
        "new_global_entry_frozen_files": frozen,
        "original_last_parent_not_restarted_and_no_global_acceptance_before_success": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})
    print("N24 final successor caches actual original B16 parent handle; full prerequisite binding",
          "and independent final audit only after its actual successful terminal", flush=True)
    wait_original(args.wait_parent_pid, output)
    for path, digest in frozen.items():
        assert sha(path) == digest
    frozen[str(ROOT / "n24-B16-final1/VERIFIED.json")] = sha(ROOT / "n24-B16-final1/VERIFIED.json")
    run_child([sys.executable, "-u", BIND_SOURCE, "--output", binding], "BINDING", output)
    frozen[str(output / "ORIGINAL-LAST-PARENT-TERMINAL.json")] = sha(output / "ORIGINAL-LAST-PARENT-TERMINAL.json")
    frozen[str(output / "BINDING-TERMINAL.json")] = sha(output / "BINDING-TERMINAL.json")
    inputspath = output / "INPUT-BINDINGS.json"
    publish(inputspath, {
        "N": 24, "new_global_entry_frozen_files": frozen,
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
        "N": 24, "actual_original_last_parent_binding_and_independent_final_audit_successfully_observed": True,
        "final_global_source_acceptance_sha256": sha(acceptedpath), "source_sha256": sha(Path(__file__)),
        "global_source_proof_closed": True,
        "scope": "qualified computer-assisted SOURCE proof; not formalization or third-party review"})


if __name__ == "__main__":
    main()
