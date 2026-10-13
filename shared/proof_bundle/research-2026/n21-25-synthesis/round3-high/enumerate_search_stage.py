"""Cross-volume input-gated paid search, followed by bounded exact union.

An old prefix is regenerated and compared, never used to skip traversal.
Search completion and union equality are separate obligations. All original
and intermediate files are retained. No target-global optimality is claimed.
"""
from pathlib import Path
import argparse
import json
import os
import struct
import subprocess
import time
from enumerate_paid_family import gates as pair_gates
from enumerate_outer_family import gates as outer_gates
from audit_paid_regression import check_subset
from merge_paid_runs_bounded import phase_metadata, finalize_runs, producer_is_active
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[2].resolve()
assert __debug__


def read(path):
    return json.loads(Path(path).read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def write_new(path, value):
    with Path(path).open("x", encoding="utf8") as stream:
        json.dump(value, stream, indent=2, ensure_ascii=True)
        stream.flush()
        os.fsync(stream.fileno())


def checked_output(path):
    registry = read(ROOT / "LARGE-OUTPUT-LOCATION.json")
    location = Path(registry["large_output_root"]).resolve()
    target = Path(path).resolve()
    assert location.exists() and target.is_relative_to(location) and target != location
    assert not target.exists(), "never overwrite a previous launch or proposed catalogue"
    assert target.parent.exists()
    return target


def check_bindings(files):
    for name, digest in files.items():
        path = Path(name)
        assert path.is_absolute() and path.is_file() and sha(path) == digest, name


def stage_gates(N, B, variant):
    const, library, table, relative = (outer_gates if variant == "outer" else pair_gates)(N, B)
    dependencies = {str((WORK / name).resolve()): digest for name, digest in relative.items()}
    basepath = ROOT / "evidence/search-stage-controls-resume1/VERIFIED.json"
    paidpath = ROOT / "evidence/search-stage-paid-controls-resume3/VERIFIED.json"
    base, paid = read(basepath), read(paidpath)
    assert base["verified"] and paid["verified"]
    assert base["source_sha256"] == sha(ROOT / "test_search_stage.py")
    assert paid["source_sha256"] == sha(ROOT / "test_search_stage_paid.py")
    assert paid["base_controls_sha256"] == sha(basepath)
    assert base["search_recursion_mechanically_preserved"]
    assert base["more_than_512_run_search_phase_completed"]
    assert base["whole_reference_set_matches_after_bounded_finalization"]
    assert base["production_block_size_also_matches"]
    assert paid["outer_nonempty_storage_full_reference_match"]
    assert {row["variant"] for row in paid["both_paid_variants_complete_regression"]} == {"pair", "outer"}
    for row in paid["both_paid_variants_complete_regression"]:
        assert row["full_set_and_stabilizers_match"]
        assert row["all_native_search_counters_and_payments_match"]
    for name, digest in base["native_sources_sha256"].items():
        assert sha(ROOT / name) == digest
    for name, digest in paid["binary_sha256"].items():
        assert sha(ROOT / name) == digest
    assert base["merge_source_sha256"] == sha(ROOT / "merge_paid_runs_bounded.py")
    binary = ROOT / ("peel_outer_search_stage.exe" if variant == "outer" else "peel_search_stage.exe")
    assert sha(binary) == base["outer_binary_sha256" if variant == "outer" else "binary_sha256"]
    extra = [Path(__file__), ROOT / "LARGE-OUTPUT-LOCATION.json", basepath, paidpath,
             ROOT / "test_search_stage.py", ROOT / "test_search_stage_paid.py",
             ROOT / "enumerate_paid_family.py", ROOT / "enumerate_outer_family.py",
             ROOT / "merge_paid_runs_bounded.py", ROOT / "paid_binary_residual.py",
             ROOT / "SEARCH-STAGE-RECOVERY.md", binary]
    extra += [ROOT / name for name in base["native_sources_sha256"]]
    for path in extra:
        dependencies[str(path.resolve())] = sha(path)
    return const, library, table, binary, dependencies


def inspect_prefix(folder, N, B, *, block_size=100000):
    """Bind every byte, accepting only the contiguous full-size old prefix.

    Header/size/hash inspection is not a mathematical row acceptance. The
    native replay will compare every retained code and stabilizer exactly.
    """
    folder = Path(folder).resolve()
    assert folder.is_dir()
    names = [path.name for path in folder.iterdir()]
    assert names and set(names) == {f"run-{i}.bin" for i in range(len(names))}
    count = 0
    entries, excluded = [], []
    first_incomplete = False
    for i in range(len(names)):
        path = folder / f"run-{i}.bin"
        with path.open("rb") as stream:
            raw = stream.read(28)
        assert len(raw) == 28 and raw[:8] == b"PAIDRUN1"
        n, b, faces, rows = struct.unpack("<IIIQ", raw[8:])
        assert (n, b, faces) == (N, B, 2*N-B-2)
        assert 0 < rows <= block_size
        expected_size = 28+rows*4*(faces+1)
        size = path.stat().st_size
        assert size <= expected_size, "extra bytes are corruption, not an interrupted suffix"
        complete = rows == block_size and size == expected_size and not first_incomplete
        entry = {"path": str(path), "sha256": sha(path), "bytes": size,
                 "declared_rows": rows, "expected_bytes": expected_size}
        if complete:
            entries.append(entry)
            count += 1
        else:
            first_incomplete = True
            excluded.append(entry)
        if (i+1) % 50 == 0:
            print("Old prefix headers, lengths and byte hashes inspected:", i+1, flush=True)
    assert count > 0
    return {"prefix_directory": str(folder), "full_prefix_runs": count,
            "accepted_for_native_exact_comparison": entries,
            "excluded_tail_files": excluded, "native_exact_comparison_not_yet_done": True,
            "search_exhaustion_proved": False}


def prefix_gates(folder, bindingpath, pid, N, B, dependencies):
    assert type(pid) is int and pid > 0 and not producer_is_active(pid)
    bindingpath = Path(bindingpath).resolve()
    old = read(bindingpath)
    assert (old["N"], old["B"]) == (N, B)
    old_files = {}
    for name, digest in old["files"].items():
        path = (WORK / name).resolve()
        assert path.is_relative_to(WORK)
        old_files[str(path)] = digest
    check_bindings(old_files)
    dependencies.update(old_files)
    dependencies[str(bindingpath)] = sha(bindingpath)
    prefix = inspect_prefix(folder, N, B)
    for entry in prefix["accepted_for_native_exact_comparison"]+prefix["excluded_tail_files"]:
        dependencies[entry["path"]] = entry["sha256"]
    prefix["old_producer_pid_confirmed_absent_or_terminal"] = pid
    prefix["old_launch_bindings_sha256"] = sha(bindingpath)
    return prefix


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, choices=(23, 24, 25), required=True)
    ap.add_argument("--B", type=int, required=True)
    ap.add_argument("--variant", choices=("pair", "outer"), required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--prefix-runs", type=Path)
    ap.add_argument("--old-bindings", type=Path)
    ap.add_argument("--old-pid", type=int)
    args = ap.parse_args()
    provided = [args.prefix_runs is not None, args.old_bindings is not None, args.old_pid is not None]
    assert all(provided) or not any(provided)
    output = checked_output(args.output)
    const, library, table, binary, dependencies = stage_gates(args.n, args.B, args.variant)
    launchcontrolpath = ROOT / "evidence/search-stage-launcher-controls-resume1/VERIFIED.json"
    launchcontrol = read(launchcontrolpath)
    assert launchcontrol["verified"] and launchcontrol["launcher_sha256"] == sha(Path(__file__))
    assert launchcontrol["source_sha256"] == sha(ROOT / "test_search_stage_launcher.py")
    assert launchcontrol["all_three_production_gates_checked"]
    assert launchcontrol["prefix_full_tail_partition_checked"]
    dependencies[str(launchcontrolpath)] = sha(launchcontrolpath)
    dependencies[str(ROOT / "test_search_stage_launcher.py")] = sha(ROOT / "test_search_stage_launcher.py")
    prefix = None
    if args.prefix_runs:
        prefix = prefix_gates(args.prefix_runs, args.old_bindings, args.old_pid,
                              args.n, args.B, dependencies)
    output.mkdir()
    if prefix:
        write_new(output / "OLD-PREFIX-INSPECTION.json", prefix)
        print("Replaying traversal from the beginning and comparing",
              prefix["full_prefix_runs"], "old full runs; not skipping old traversal.", flush=True)
    target = output / f"N{args.n}-B{args.B}-{args.variant}-search.bin"
    command = [str(binary), str(args.n), str(args.B), str(target),
               str(const["angle_scale"]), *map(str, const["angle_caps"]), "0", "dfs", str(table),
               prefix["prefix_directory"] if prefix else "-",
               str(prefix["full_prefix_runs"]) if prefix else "0"]
    bindingpath = output / "INPUT-BINDINGS.json"
    write_new(bindingpath, {"N": args.n, "B": args.B, "variant": args.variant,
                           "command": command, "files_absolute": dependencies,
                           "search_completed": False, "global_optimality_proved": False})
    started = time.monotonic()
    with (output / "NATIVE-STDERR.log").open("xb") as log:
        process = subprocess.Popen(command, cwd=ROOT, stdout=log, stderr=log,
                                   creationflags=subprocess.CREATE_NO_WINDOW)
        write_new(output / "NATIVE-LAUNCH.json", {"native_pid": process.pid, "command": command,
                  "input_bindings_sha256": sha(bindingpath), "native_terminal_observed": False})
        print("New staged native search launched:", args.n, args.B, args.variant,
              "PID", process.pid, "output", str(output), flush=True)
        code = process.wait()
    terminal = {"native_pid": process.pid, "native_terminal_observed": True, "native_exit_code": code,
                "native_stderr_sha256": sha(output / "NATIVE-STDERR.log"),
                "input_bindings_sha256": sha(bindingpath),
                "seconds": time.monotonic()-started, "global_optimality_proved": False}
    write_new(output / "NATIVE-TERMINAL.json", terminal)
    assert code == 0, "failed or interrupted search is not accepted"
    check_bindings(dependencies)
    metadata = phase_metadata(Path(str(target)+".building"))
    assert (metadata["N"], metadata["B"], metadata["mode"]) == (args.n, args.B, "dfs")
    assert metadata["native_search_only_stage"] and metadata["screen"]
    assert metadata["scale"] == const["angle_scale"] and metadata["caps"] == const["angle_caps"]
    assert metadata["survivor_block_size"] == 100000
    expected_prefix_count = prefix["full_prefix_runs"] if prefix else 0
    assert metadata["prefix_runs_replayed_and_compared"] == expected_prefix_count
    paths = [Path(str(target)+".runs") / f"run-{i}.bin" for i in range(metadata["run_count"])]
    assert {p.name for p in Path(str(target)+".runs").iterdir()} == {p.name for p in paths}
    if prefix:
        for i, entry in enumerate(prefix["accepted_for_native_exact_comparison"]):
            assert sha(paths[i]) == entry["sha256"]
    byid = {row["id"]: row for row in library["obstacles"]}
    for payment in metadata["proof_payments"]:
        obstacle = byid[payment["obstacle"]]
        assert obstacle["B"] == args.B
        mapping = {key: payment[key] for key in ("centers", "anchors", "orientation", "shift")}
        check_subset(args.n, args.B, obstacle, mapping, set(payment["sample_faces"]))
    write_new(output / "SEARCH-COMPLETE.json", {
        "verified": True, "N": args.n, "B": args.B, "native_exhaustive_search_terminated_successfully": True,
        "old_prefix_runs_regenerated_and_compared": expected_prefix_count,
        "run_count": metadata["run_count"], "rows_to_runs": metadata["rows_to_runs"],
        "phase_sha256": sha(Path(str(target)+".building")),
        "terminal_sha256": sha(output / "NATIVE-TERMINAL.json"),
        "input_bindings_sha256": sha(bindingpath), "source_sha256": sha(Path(__file__)),
        "unique_catalogue_finalized": False, "global_optimality_proved": False})
    print("Native SEARCH complete; beginning bounded exact finalization:", args.n, args.B, flush=True)
    final, union = finalize_runs(paths, metadata, output / "bounded-finalization", fan_in=32)
    write_new(output / "UNION-VERIFIED.json", union)
    check_bindings(dependencies)
    report = {"verified": True, "N": args.n, "B": args.B, "variant": args.variant,
              "complete_residual_family_search": True, "full_unpruned_catalogue_enumerated": False,
              "all_sorted_run_union_equality_verified": True,
              "residual_orbits": union["residual_orbits"], "calls": metadata["calls"],
              "old_prefix_runs_regenerated_and_compared": expected_prefix_count,
              "pruned_recursive_states_not_orbit_count": metadata["proof_prunes"],
              "native_guard_source_argument_required_for_all_prunes": True,
              "payment_samples_independently_mapped": len(metadata["proof_payments"]),
              "catalog_absolute_path": str(final), "catalog_sha256": sha(final),
              "search_receipt_sha256": sha(output / "SEARCH-COMPLETE.json"),
              "union_receipt_sha256": sha(output / "UNION-VERIFIED.json"),
              "input_bindings_sha256": sha(bindingpath), "files_absolute": dependencies,
              "source_sha256": sha(Path(__file__)), "seconds": time.monotonic()-started,
              "all_residual_types_lower_bounds_paid": union["residual_orbits"] == 0,
              "global_optimality_proved": False,
              "scope": "necessary family = certified-pruned branches + complete unpaid residual catalogue"}
    write_new(output / "SUMMARY.json", report)
    print("Complete residual search AND independently checked bounded union:", args.n, args.B,
          union["residual_orbits"], "unpaid residual types; not target-global optimality", flush=True)


if __name__ == "__main__":
    main()
