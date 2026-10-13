"""Reaccept original historical launch/source gates and fresh complete union.

The archived terminal record is not a current PID. All exact historical input
bytes are remapped explicitly and rehashed. No native search is restarted.
This establishes the recorded necessary family, not any residual lower bound.
"""
from pathlib import Path, PureWindowsPath
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from enumerate_search_stage import stage_gates
from merge_paid_runs_bounded import phase_metadata

assert __debug__
WORK = ROOT.parents[2]


def main():
    ap = argparse.ArgumentParser()
    for name in ("assets", "union", "inventory", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    assets, unionpath, inventorypath, output = (getattr(args, name).resolve()
                                               for name in ("assets", "union", "inventory", "output"))
    assert all(path.is_relative_to(ROOT) for path in (assets, unionpath, inventorypath, output))
    assert not output.exists()
    recoverypath = assets / "VERIFIED.json"
    recovered, union, inventory = map(read, (recoverypath, unionpath, inventorypath))
    assert recovered["verified"] and recovered["schema"] == "isolated-N23-B14-all-original-union-asset-byte-recovery-v1"
    assert recovered["source_sha256"] == sha(ROOT / "recover_n23_B14_union_assets.py")
    assert union["verified"] and union["schema"] == "independent-restored-N23-B14-all-retained-run-hierarchical-union-v1"
    assert union["source_sha256"] == sha(ROOT / "audit_n23_B14_restored_union.py")
    assert union["all_779_original_runs_entirely_scanned_and_union_compared"]
    assert union["all_25_layer_inputs_entirely_compared_against_final_catalog"]
    assert union["every_hierarchical_batch_exact_complete_union_equality_verified"]
    assert union["all_original_and_intermediate_bytes_unchanged_after_acceptance"]
    assert (union["N"], union["B"], union["original_rows"], union["residual_orbits"]) == (
        23, 14, 77892318, 8277632)
    for path, digest in union["frozen_files"].items():
        assert sha(path) == digest
    assert inventory["schema"] == "historical-N23-B14-explicit-root-launch-byte-inventory-v1"
    assert inventory["source_sha256"] == sha(ROOT / "inspect_n23_B14_launch_dependency_bytes.py")
    assert inventory["counts"] == {"original-byte-sha256-matches": 8726}
    assert inventory["all_8726_old_dependency_names_accounted_for_once"]
    source = assets / "SOURCE"
    bindingpath = source / "INPUT-BINDINGS.json"
    binding, terminal, complete, launch = map(read, (
        bindingpath, source / "NATIVE-TERMINAL.json", source / "SEARCH-COMPLETE.json",
        source / "NATIVE-LAUNCH.json"))
    assert inventory["binding_sha256"] == sha(bindingpath)
    assert inventory["recovery_report_sha256"] == sha(recoverypath)
    assert len(binding["files_absolute"]) == len(inventory["entries"]) == 8726
    oldroot = PureWindowsPath(inventory["historical_source_root"])
    assert oldroot.is_absolute() and str(WORK) == inventory["mapped_current_workspace"]
    mapped = {}
    for row in inventory["entries"]:
        old = row["old_absolute_path"]
        assert binding["files_absolute"][old] == row["expected_sha256"]
        path = PureWindowsPath(old)
        assert path.is_relative_to(oldroot)
        relative = path.relative_to(oldroot)
        assert ".." not in relative.parts
        target = (WORK / Path(*relative.parts)).resolve()
        assert target.is_relative_to(WORK) and str(target) == row["mapped_absolute_path"]
        assert target not in mapped and sha(target) == row["expected_sha256"]
        mapped[target] = row["expected_sha256"]
    assert len(mapped) == 8726
    constants, library, table, binary, production = stage_gates(23, 14, "pair")
    assert all(mapped[Path(path)] == digest for path, digest in production.items())
    launchcontrolpath = HIGH / "evidence/search-stage-launcher-controls-resume1/VERIFIED.json"
    launchcontrol = read(launchcontrolpath)
    assert launchcontrol["verified"] and launchcontrol["all_three_production_gates_checked"]
    assert launchcontrol["prefix_full_tail_partition_checked"]
    assert launchcontrol["launcher_sha256"] == sha(HIGH / "enumerate_search_stage.py")
    assert launchcontrol["source_sha256"] == sha(HIGH / "test_search_stage_launcher.py")
    extra = {launchcontrolpath, HIGH / "test_search_stage_launcher.py"}
    assert set(mapped) == {Path(path) for path in production} | extra
    command = binding["command"]
    assert len(command) == 13 and command[1:3] == ["23", "14"]
    assert command[4:10] == [
        str(constants["angle_scale"]), *map(str, constants["angle_caps"]), "0", "dfs"]
    assert command[-2:] == ["-", "0"]
    for token, target in ((command[0], binary), (command[10], table)):
        old = PureWindowsPath(token)
        assert old.is_relative_to(oldroot)
        assert (WORK / Path(*old.relative_to(oldroot).parts)).resolve() == target.resolve()
    assert PureWindowsPath(command[3]).name == "N23-B14-pair-search.bin"
    assert launch["command"] == command and launch["input_bindings_sha256"] == sha(bindingpath)
    assert terminal["native_pid"] == launch["native_pid"]
    assert terminal["native_terminal_observed"] and terminal["native_exit_code"] == 0
    assert terminal["input_bindings_sha256"] == sha(bindingpath)
    assert terminal["native_stderr_sha256"] == sha(source / "NATIVE-STDERR.log")
    assert complete["phase_sha256"] == sha(source / "N23-B14-pair-search.bin.building")
    assert complete["terminal_sha256"] == sha(source / "NATIVE-TERMINAL.json")
    assert complete["input_bindings_sha256"] == sha(bindingpath)
    assert complete["source_sha256"] == sha(HIGH / "enumerate_search_stage.py")
    assert complete["verified"] and complete["native_exhaustive_search_terminated_successfully"]
    phase = phase_metadata(source / "N23-B14-pair-search.bin.building")
    assert phase["native_search_only_stage"] and phase["screen"] and phase["root_degree_prune"]
    assert phase["scale"] == constants["angle_scale"] and phase["caps"] == constants["angle_caps"]
    assert phase["survivor_block_size"] == 100000 and phase["mode"] == "dfs"
    assert phase["run_count"] == complete["run_count"] == 779
    assert phase["rows_to_runs"] == complete["rows_to_runs"] == union["original_rows"]
    assert phase["proof_prunes"] == 0 and phase["proof_payments"] == []
    assert phase["prefix_runs_replayed_and_compared"] == complete["old_prefix_runs_regenerated_and_compared"] == 0
    kernel = (HIGH / "peel_search_stage_kernel.inc").read_text(encoding="utf8")
    assert kernel.index("if(possible(initial))visit(initial,{{boundary,n-b}});else prunes++;") < kernel.index(
        " auto row_count=write_search_phase(mode);")
    storage = (HIGH / "paid_search_stage_storage.inc").read_text(encoding="utf8")
    phase_start = storage.index("uint64_t write_search_phase")
    assert storage.index(" flush_paid_run();", phase_start) < storage.index('out.write("PAIDRSV1",8)', phase_start)
    assert storage.index("requested resume prefix was not fully regenerated", phase_start) < storage.index(
        'out.write("PAIDRSV1",8)', phase_start)
    catalogpath = ROOT / union["catalog_relative_to_round4"]
    assert sha(catalogpath) == union["catalog_sha256"]
    files = {str(path): digest for path, digest in mapped.items()}
    files.update(union["frozen_files"])
    for path in (
        Path(__file__).resolve(), recoverypath, unionpath, inventorypath, bindingpath, catalogpath,
        source / "SEARCH-COMPLETE.json", source / "NATIVE-TERMINAL.json",
        HIGH / "PROOF-AWARE-PEELING.md", HIGH / "SEARCH-STAGE-RECOVERY.md",
        ROOT / "N23-N24-UNEXPOSED-ORIGIN-SOURCE.md"):
        files[str(path)] = sha(path)
    for path, digest in files.items():
        assert sha(path) == digest
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "restored-N23-B14-historical-complete-source-and-fresh-union-gates-v1",
        "N": 23, "B": 14, "complete_recorded_necessary_family": True,
        "residual_orbits": 8277632, "catalog_sha256": sha(catalogpath),
        "catalog_relative_to_round4": catalogpath.relative_to(ROOT).as_posix(),
        "all_8726_original_launch_dependencies_explicitly_remapped_and_rehashed": True,
        "original_production_math_library_storage_and_launcher_gates_freshly_checked": True,
        "full_root_node_limit_zero_dfs_no_seed_no_prefix_checked": True,
        "historical_actual_native_zero_terminal_phase_and_source_order_checked": True,
        "all_original_and_layer_inputs_fresh_complete_union_verified": True,
        "no_paid_pruned_state_in_this_historical_phase": True,
        "old_native_pid_is_historical_not_a_live_process_identity": True,
        "completeness_uses_original_written_peeling_and_safe_pruning_induction": True,
        "not_a_new_native_enumeration_or_third_party_review": True,
        "all_residual_type_lower_bounds_not_paid_by_source_or_union": True,
        "arbitrary_cover_reduction_exact_upper_and_other_families_still_required": True,
        "frozen_files": files, "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("Original N23/B14 necessary source and full union gates reaccepted:",
          8277632, "types; their lower bounds not paid here", flush=True)


if __name__ == "__main__":
    main()
