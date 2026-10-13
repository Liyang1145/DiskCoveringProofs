"""Actual original binding terminal, then independent complete current-content audit.

The final theorem is a computer-assisted source proof with reviewed written
mathematics and exact accepted computations, not a formal proof of prose.
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

assert __debug__
DOCUMENT = ROOT / "N23-GLOBAL-SOURCE-PROOF-v1.md"
CHAIN = ROOT / "n23-B15-whole-final-chain-v1/VERIFIED.json"
SOURCE = ROOT / "n23-three-full-source-interfaces-v2/VERIFIED.json"


def premise_gate(binding, chain, source):
    assert binding["verified"]
    assert binding["schema"] == "N23-complete-three-family-source-lower-root-current-premise-byte-closure-v1"
    assert binding["N"] == 23 and binding["required_boundary_families"] == [13, 14, 15]
    assert binding["complete_original_catalog_counts"] == [1530509, 8277632, 16790546]
    assert binding["all_original_catalog_lower_payment_chains_formally_zero"]
    assert binding["actual_same_root_upper_budget_local_and_core_transport_prerequisites_linked"]
    assert binding["all_current_content_bindings_checked"] and not binding["mismatches"]
    assert binding["B13_original_all670428_member_byte_theorem_reused_under_unchanged_full_archive_and_local_hashes"]
    assert binding["old_mathematics_reused_unchanged_not_claimed_new_fresh_all_tree_replay"]
    assert binding["source_sha256"] == sha(ROOT / "bind_n23_all_final_prerequisites.py")
    assert chain["verified"] and chain["N"] == 23 and chain["B"] == 15
    assert chain["original_catalog_types"] == 16790546 and chain["pending_types"] == 0
    assert chain["every_parent_hash_pending_count_and_disjoint_increment_checked"]
    assert chain["complete_candidate_actual_source_map_and_active_root_graph_freshly_rechecked"]
    assert chain["actual_full_strict_types"] == 828 and chain["actual_full_same_root_nonstrict_types"] == 1
    assert chain["source_sha256"] == sha(ROOT / "verify_n23_B15_final_chain.py")
    assert source["verified"] and source["N"] == 23
    assert source["families"] == [[13, 10], [14, 9], [15, 8]]
    assert source["b13_and_b14_actual_zero_paid_prunes_no_hidden_library_skips"]
    assert source["b15_actual_original_cpp_binary_degree_controls_and_complete_stream_driver_bound"]
    assert source["written_cover_transport_and_full_induction_are_reviewed_math_premises_not_hash_proofs"]
    assert source["source_sha256"] == sha(ROOT / "verify_n23_full_source_interfaces.py")


def control_gate(binding, chain, source):
    premise_gate(binding, chain, source)
    refused = []
    def check(name, wrong_binding=binding, wrong_chain=chain, wrong_source=source):
        try:
            premise_gate(wrong_binding, wrong_chain, wrong_source)
        except (AssertionError, KeyError):
            refused.append(name)
        else:
            raise AssertionError("incorrect global source premise accepted: "+name)
    for field, value in (
        ("verified", False), ("N", 24), ("required_boundary_families", [13, 15]),
        ("complete_original_catalog_counts", [1530509, 8277631, 16790546]),
        ("all_original_catalog_lower_payment_chains_formally_zero", False),
        ("actual_same_root_upper_budget_local_and_core_transport_prerequisites_linked", False),
        ("all_current_content_bindings_checked", False),
        ("mismatches", [{"path": "bad"}]),
        ("B13_original_all670428_member_byte_theorem_reused_under_unchanged_full_archive_and_local_hashes", False)):
        wrong = deepcopy(binding)
        wrong[field] = value
        check("binding-"+field, wrong_binding=wrong)
    for field, value in (("pending_types", 1), ("actual_full_same_root_nonstrict_types", 0),
                         ("complete_candidate_actual_source_map_and_active_root_graph_freshly_rechecked", False)):
        wrong = deepcopy(chain)
        wrong[field] = value
        check("chain-"+field, wrong_chain=wrong)
    for field, value in (("families", [[13, 10], [15, 8]]),
                         ("b13_and_b14_actual_zero_paid_prunes_no_hidden_library_skips", False)):
        wrong = deepcopy(source)
        wrong[field] = value
        check("source-"+field, wrong_source=wrong)
    assert len(refused) == 14
    return refused


def audit(bindingdir, expected_inputs, output):
    assert not output.exists()
    before = read(expected_inputs)
    for path, digest in before["new_global_entry_frozen_files"].items():
        assert sha(path) == digest
    bindingpath = bindingdir / "VERIFIED.json"
    binding, chain, source = read(bindingpath), read(CHAIN), read(SOURCE)
    refused = control_gate(binding, chain, source)
    ledger = bindingdir / "CURRENT-INPUTS.jsonl"
    assert sha(ledger) == binding["current_input_ledger_sha256"]
    archives = bindingdir / "ARCHIVE-ONLY-DEPENDENCIES.json"
    assert sha(archives) == binding["archive_only_dependency_ledger_sha256"]
    for path, digest in binding["explicit_entry_report_hashes"].items():
        assert sha(path) == digest
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
                print("N23 final independent entire source-proof byte audit", count,
                      "/", binding["current_files_and_whole_archives_checked"],
                      "differences", len(mismatches), flush=True)
    assert count == binding["current_files_and_whole_archives_checked"]
    assert not mismatches, mismatches
    assert sha(ledger) == binding["current_input_ledger_sha256"]
    for path, digest in chain["frozen_files"].items():
        assert sha(path) == digest
    for path, digest in before["new_global_entry_frozen_files"].items():
        assert sha(path) == digest
    rootproof = read(ROOT / "n23-nonstrict-core-fresh-root-upper-local-angle-audit-solo-v1/VERIFIED.json")
    root = read(ROOT / "n23-nonstrict-core-fresh-root-upper-local-angle-audit-solo-v1/root-verified.json")
    assert root["root_sha256"] == rootproof["root_sha256"] and root["system_sha256"] == rootproof["system_sha256"]
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "GLOBAL-SOURCE-ACCEPTED.json", {
        "verified": True, "schema": "N23-arbitrary-unit-closed-disk-cover-global-computer-assisted-source-proof-v1",
        "N": 23, "theorem": "r_D(23)=R",
        "exact_R": "positive square root of t in the isolated unique234-variable own root system; not a float",
        "root_sha256": rootproof["root_sha256"], "system_sha256": rootproof["system_sha256"],
        "strict_radius_interval": root["r_strict_interval"],
        "arbitrary_plane_centers_repetitions_fewer_disks_and_degeneracies_allowed": True,
        "no_symmetry_or_fixed_contact_graph_assumed": True,
        "same_exact_root_entire_closed_disk_upper_and_all_necessary_family_lower_proofs": True,
        "required_boundary_families": [13, 14, 15],
        "complete_original_catalog_counts": [1530509, 8277632, 16790546],
        "complete_original_catalog_types": 26598687,
        "every_original_catalog_type_paid_with_actual_cover_necessity_strict_or_same_root_core": True,
        "all_pending_types": 0, "actual_full_nonstrict_core_types": 1,
        "written_cover_peeling_and_local_quadratic_mathematics_reviewed_as_source_proof_premises": True,
        "written_math_not_claimed_machine_proved_by_hash_check": True,
        "all_old_exact_mathematics_honestly_reused_under_unchanged_full_content_bindings": True,
        "current_files_and_whole_archives_independently_rechecked": count,
        "B13_all670428_original_members_bound_in_original_current_root_or_verified_whole_archives": True,
        "old_E_paths_not_rewritten_and_archive_only_members_not_claimed_current_local_files": True,
        "source_document_sha256": sha(DOCUMENT),
        "all_prerequisites_binding_sha256": sha(bindingpath),
        "B15_whole_chain_and_actual_full_core_transport_sha256": sha(CHAIN),
        "three_full_source_interfaces_sha256": sha(SOURCE),
        "frozen_input_ledger_sha256": sha(output / "FROZEN-INPUTS.jsonl"),
        "new_global_entry_frozen_files": before["new_global_entry_frozen_files"],
        "negative_global_scope_controls_rejected": refused,
        "source_sha256": sha(Path(__file__)),
        "not_Lean_Coq_formalization_not_third_party_peer_review_not_all_attaining_configurations_classified": True,
        "global_source_proof_closed": True, "global_optimality_proved": True,
    })
    print("N23 arbitrary-cover global computer-assisted SOURCE proof final acceptance complete;",
          "not Lean/Coq or third-party review; old math reused transparently", flush=True)


def wait_original(pid, output):
    assert os.name == "nt" and type(pid) is int and pid > 0
    script = r"""
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
$ErrorActionPreference = 'Stop'
$taskProcess = Get-Process -Id TASK_PID
$taskHandle = $taskProcess.Handle
$taskStart = $taskProcess.StartTime.ToUniversalTime().ToFileTimeUtc()
$taskInfo = Get-CimInstance Win32_Process -Filter 'ProcessId = TASK_PID'
if ($null -eq $taskInfo) { throw 'Original binding process identity unavailable' }
if ([decimal]::Floor(([decimal]$taskStart) / 10) -ne [decimal]::Floor(([decimal]$taskInfo.CreationDate.ToUniversalTime().ToFileTimeUtc()) / 10)) {
    throw 'Original PID creation identity differs'
}
if ($taskInfo.Name -ne 'python.exe') { throw 'Wrong original binding image' }
if (-not $taskInfo.CommandLine.Contains('bind_n23_all_final_prerequisites.py')) { throw 'Wrong original binding source' }
if (-not $taskInfo.CommandLine.Contains('n23-all-final-prerequisites-byte-binding-v1')) { throw 'Wrong original binding output' }
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
    publish(output / "ORIGINAL-BINDING-TERMINAL.json", terminal)
    assert terminal["OriginalPid"] == pid
    assert terminal["OriginalCachedProcessHandleTerminalObserved"] and terminal["ActualExitCode"] == 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--audit-only", action="store_true")
    ap.add_argument("--binding", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--inputs", type=Path)
    ap.add_argument("--wait-pid", type=int)
    args = ap.parse_args()
    binding, output = args.binding.resolve(), args.output.resolve()
    assert binding.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    if args.audit_only:
        assert args.inputs is not None
        audit(binding, args.inputs.resolve(), output)
        return
    assert args.wait_pid is not None
    frozen = {str(path): sha(path) for path in (
        Path(__file__), DOCUMENT, CHAIN, SOURCE,
        ROOT / "bind_n23_all_final_prerequisites.py",
        ROOT / "verify_n23_B15_final_chain.py",
        ROOT / "N23-N24-COVER-AND-FULL-PEEL-INDUCTION-v1.md",
        ROOT / "N23-SAME-ROOT-CORE-AND-GLOBAL-ASSEMBLY-INTERFACE-v1.md")}
    output.mkdir()
    inputspath = output / "INPUT-BINDINGS.json"
    publish(inputspath, {
        "N": 23, "original_binding_pid": args.wait_pid,
        "new_global_entry_frozen_files": frozen,
        "original_binding_not_restarted_and_no_global_acceptance_before_success": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})
    print("N23 final global-source successor caches original binding handle; final independent",
          "all-content audit only after actual original successful terminal", flush=True)
    wait_original(args.wait_pid, output)
    premise_gate(read(binding / "VERIFIED.json"), read(CHAIN), read(SOURCE))
    with (output / "FINAL-AUDIT-STDOUT.log").open("xb") as stdout, \
            (output / "FINAL-AUDIT-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen(list(map(str, [
            sys.executable, "-u", Path(__file__), "--audit-only", "--binding", binding,
            "--inputs", inputspath, "--output", output / "ACCEPTED"])),
            cwd=str(ROOT), stdout=stdout, stderr=stderr, creationflags=subprocess.CREATE_NO_WINDOW)
        code = process.wait()
    publish(output / "FINAL-AUDIT-TERMINAL.json", {
        "pid": process.pid, "actual_exit_code": code,
        "actual_independent_child_terminal_observed": True, "source_sha256": sha(Path(__file__))})
    assert code == 0
    for path, digest in frozen.items():
        assert sha(path) == digest
    acceptedpath = output / "ACCEPTED/GLOBAL-SOURCE-ACCEPTED.json"
    accepted = read(acceptedpath)
    assert accepted["verified"] and accepted["global_source_proof_closed"]
    publish(output / "PIPELINE-COMPLETED.json", {
        "N": 23, "actual_original_binding_and_independent_final_audit_successfully_observed": True,
        "final_global_source_acceptance_sha256": sha(acceptedpath),
        "source_sha256": sha(Path(__file__)), "global_source_proof_closed": True,
        "scope": "qualified computer-assisted SOURCE proof; not formalization or third-party review"})


if __name__ == "__main__":
    main()
