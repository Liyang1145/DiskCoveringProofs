"""New-root n25/B14 outer-obstacle search, with all original kernels unchanged.

New library data is reaccepted. All native filesystem arguments are ASCII
relative paths. Stages, termination and full bounded union remain separate.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import gzip
import json
import os
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
WORK = ROOT.parents[2].resolve()
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys
from merge_paid_runs_bounded import phase_metadata, finalize_runs
from audit_streamed_hierarchy import check_map

assert __debug__


def read(path):
    return json.loads(Path(path).read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def publish(path, data):
    with path.open("x", encoding="utf8") as stream:
        json.dump(data, stream, indent=2, ensure_ascii=True)
        stream.flush()
        os.fsync(stream.fileno())


def relarg(path):
    path = Path(path).resolve()
    relative = os.path.relpath(path, HIGH).replace("\\", "/")
    assert relative.isascii()
    return relative


def bind(files, path):
    path = Path(path).resolve()
    assert path.is_relative_to(WORK)
    files[path.relative_to(WORK).as_posix()] = sha(path)


def unchanged(files):
    for name, digest in files.items():
        assert sha(WORK / name) == digest, ("bound input changed", name)


def library_gate(path):
    lib = read(path)
    constpath = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    const = read(constpath)
    assert const["N"] == 25 and const["verified"] and [14, 11] in const["families"]
    assert const["minimum_interior_cells"] == 8 and const["minimum_boundary_cells"] == 14
    assert const["families"] == [[b, 25-b] for b in range(14, 18)]
    U = F(const["radius_upper"])
    assert U < F(1, 4) and U/(1-2*U) < F(1, 2)
    sys.path.insert(0, str(exact.kernel.ARCS))
    import exact_arcs as arcs
    assert U < F(arcs.sincos_turn(F(1, 26))[1][0], arcs.SCALE)
    assert const["angle_scale"] == 10**7
    for k, cap in enumerate(const["angle_caps"], 1):
        assert F(arcs.sincos_turn(F(cap, 2*const["angle_scale"]))[1][0], arcs.SCALE) > k*U
    assert lib["verified"] and lib["schema"] == "strict-outer-obstacle-library-v1"
    assert lib["source_N"] == 25 and lib["threshold"] == 1
    assert lib["no_root_or_local_theorem_used"] and lib["all_library_trees_fresh_exact_replayed"]
    assert F(lib["radius_threshold"]) == F(const["radius_upper"])
    assert lib["source_sha256"] == sha(ROOT / "export_n25_outer_library.py")
    table = path.parent / "OBSTACLES.tsv"
    assert sha(table) == lib["pattern_table_sha256"]
    files = dict(lib["files"])
    unchanged(files)
    lines = table.read_text(encoding="ascii").splitlines()
    assert lines[0] == lib["schema"] and len(lines) == lib["obstacle_count"] + 1
    assert len(lib["obstacles"]) == lib["obstacle_count"] > 0
    for index, obstacle in enumerate(lib["obstacles"]):
        assert obstacle["id"] == index and obstacle["B"] == 14
        faces, centers = obstacle["faces"], obstacle["centers"]
        assert 14 <= centers <= 25 and faces == sorted(set(faces))
        assert list(map(int, lines[index + 1].split())) == [index, 14, centers, len(faces), *faces]
        assert all((mask & ((1 << 14)-1)).bit_count() >= 1 for mask in faces)
        treepath = WORK / obstacle["tree_file_relative_to_workspace"]
        assert sha(treepath) == obstacle["tree_sha256"]
        with gzip.open(treepath, "rt", encoding="utf8") as stream:
            tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
        assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (25, 14, centers, faces)
        assert tree["constants_sha256"] == sha(constpath)
        assert all(n["kind"] in ("EMPTY", "SPLIT", "DUAL") for n in tree["nodes"])
        result = exact.verify(14, centers, faces, tree["nodes"], const)
        assert result == obstacle["fresh_exact_replay"]
    for p in (path, table, constpath, Path(__file__)):
        bind(files, p)
    return const, lib, table, files


def kernel_gate(files):
    stagepath = HIGH / "evidence/search-stage-controls-resume1/VERIFIED.json"
    outerpath = HIGH / "evidence/outer-paid-controls-resume1/VERIFIED.json"
    stage, outer = read(stagepath), read(outerpath)
    assert stage["verified"] and outer["verified"]
    assert stage["search_recursion_mechanically_preserved"]
    assert stage["more_than_512_run_search_phase_completed"]
    assert stage["whole_reference_set_matches_after_bounded_finalization"]
    assert outer["outer_kernel_threshold_derivation_verified"] and outer["nontrivial_all_missing_types_paid"]
    assert stage["source_sha256"] == sha(HIGH / "test_search_stage.py")
    assert outer["source_sha256"] == sha(HIGH / "test_outer_paid.py")
    assert stage["outer_binary_sha256"] == sha(HIGH / "peel_outer_search_stage.exe")
    assert stage["merge_source_sha256"] == sha(HIGH / "merge_paid_runs_bounded.py")
    assert outer["matcher_binary_sha256"] == sha(HIGH / "peel_outer_match.exe")
    for control in (stage, outer):
        for name, digest in control["native_sources_sha256"].items():
            assert sha(HIGH / name) == digest
            bind(files, HIGH / name)
    # Mechanical recursion/threshold preservation is rechecked, not a status bit.
    import test_paid_storage
    test_paid_storage.check_stream_derivation()
    baseline = (HIGH / "peel_paid_stream_kernel.inc").read_text(encoding="utf8")
    changes = [
        ('#include "paid_matcher.inc"\n#include "paid_stream_storage.inc"',
         '#ifndef PAID_STAGE_OUTER\n#include "paid_matcher.inc"\n#else\n#include "paid_outer_matcher.inc"\n#endif\n#include "paid_search_stage_storage.inc"'),
        ('if(argc!=11)throw runtime_error("usage: paid-peel N B output scale cap2 cap4 cap6 node-limit mode paid-table-or-minus");',
         'if(argc!=13)throw runtime_error("usage: search-stage N B output scale cap2 cap4 cap6 node-limit mode paid-table-or-minus prefix-runs-or-minus prefix-count");'),
        ('load_obstacles(argv[10]);',
         'load_obstacles(argv[10]);\n replay_prefix_directory=argv[11];replay_prefix_count=stoull(argv[12]);\n if((replay_prefix_directory=="-")!=(replay_prefix_count==0))\n  throw runtime_error("prefix directory/count mismatch");'),
        (' auto unique_count=merge_paid_runs(mode);\n cerr<<"RESIDUAL COMPLETE B="<<b<<" calls="<<calls<<" orbits="<<unique_count<<" proof_prunes="<<proof_prunes<<"\\n";',
         ' auto row_count=write_search_phase(mode);\n cerr<<"SEARCH COMPLETE B="<<b<<" calls="<<calls<<" run_rows="<<row_count<<" proof_prunes="<<proof_prunes\n     <<" prefix_runs_compared="<<replay_prefix_runs_compared<<"\\n";'),
    ]
    for old, new in changes:
        assert baseline.count(old) == 1
        baseline = baseline.replace(old, new, 1)
    assert baseline == (HIGH / "peel_search_stage_kernel.inc").read_text(encoding="utf8")
    matcher = (HIGH / "paid_matcher.inc").read_text(encoding="utf8")
    for old, new in [
        ("strict-obstacle-library-v1", "strict-outer-obstacle-library-v1"),
        ("pop(uint32_t(mask)&((uint32_t(1)<<B)-1))<2", "pop(uint32_t(mask)&((uint32_t(1)<<B)-1))<1"),
        ("pop(face&((uint32_t(1)<<b)-1))>=2", "pop(face&((uint32_t(1)<<b)-1))>=1"),
    ]:
        assert matcher.count(old) == 1
        matcher = matcher.replace(old, new, 1)
    assert matcher == (HIGH / "paid_outer_matcher.inc").read_text(encoding="utf8")
    for p in (stagepath, outerpath, HIGH / "test_search_stage.py", HIGH / "test_outer_paid.py",
              HIGH / "test_paid_storage.py", HIGH / "peel_outer_search_stage.exe",
              HIGH / "peel_outer_match.exe", HIGH / "merge_paid_runs_bounded.py",
              HIGH / "paid_binary_residual.py", HIGH / "audit_streamed_hierarchy.py",
              HIGH / "PROOF-AWARE-PEELING.md", HIGH / "PROOF-AWARE-OUTER-PEELING.md",
              ROOT / "N25-OUTER-OBSTACLE-TRANSPORT.md"):
        bind(files, p)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--controls", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT.resolve()) and output != ROOT.resolve() and not output.exists()
    const, lib, table, files = library_gate(args.library.resolve())
    kernel_gate(files)
    controls = read(args.controls)
    assert controls["verified"] and controls["library_sha256"] == sha(args.library)
    assert controls["source_sha256"] == sha(ROOT / "test_n25_outer_library.py")
    assert controls["search_runner_sha256"] == sha(Path(__file__))
    assert controls["all_library_transformed_maps_checked"] and controls["node_limit_cannot_publish"]
    bind(files, args.controls)
    bind(files, ROOT / "test_n25_outer_library.py")
    output.mkdir(parents=True)
    target = output / "N25-B14-outer-search.bin"
    command = [str(HIGH / "peel_outer_search_stage.exe"), "25", "14", relarg(target),
               str(const["angle_scale"]), *map(str, const["angle_caps"]), "0", "dfs", relarg(table), "-", "0"]
    publish(output / "INPUT-BINDINGS.json", {
        "N": 25, "B": 14, "files_relative_to_workspace": files, "command": command,
        "new_search_with_new_strict_library": True, "old_unfinished_runs_preserved": True,
        "no_prefix_skipped_or_claimed_resumed": True, "global_optimality_proved": False,
    })
    started = time.monotonic()
    disk_stop = False
    with (output / "NATIVE-STDERR.log").open("xb") as log:
        process = subprocess.Popen(command, cwd=HIGH, stdout=log, stderr=log,
                                   creationflags=subprocess.CREATE_NO_WINDOW)
        publish(output / "NATIVE-LAUNCH.json", {
            "native_pid": process.pid, "command": command, "input_bindings_sha256": sha(output / "INPUT-BINDINGS.json"),
            "native_terminal_observed": False,
        })
        print("N25/B14 strict outer search launched:", process.pid, "obstacles", len(lib["obstacles"]), flush=True)
        while True:
            try:
                code = process.wait(timeout=30)
                break
            except subprocess.TimeoutExpired:
                if shutil.disk_usage(output).free < 12 * 1024**3:
                    disk_stop = True
                    process.terminate()
                    code = process.wait(timeout=30)
                    break
    publish(output / "NATIVE-TERMINAL.json", {
        "native_pid": process.pid, "native_terminal_observed": True, "native_exit_code": code,
        "stopped_for_disk_reserve": disk_stop, "seconds": time.monotonic() - started,
        "log_sha256": sha(output / "NATIVE-STDERR.log"), "global_optimality_proved": False,
    })
    assert code == 0 and not disk_stop, "interrupted search is incomplete, never accepted"
    unchanged(files)
    phase = Path(str(target) + ".building")
    meta = phase_metadata(phase)
    assert (meta["N"], meta["B"], meta["mode"]) == (25, 14, "dfs")
    assert meta["native_search_only_stage"] and meta["prefix_runs_replayed_and_compared"] == 0
    assert meta["scale"] == const["angle_scale"] and meta["caps"] == const["angle_caps"]
    for payment in meta["proof_payments"]:
        obstacle = lib["obstacles"][payment["obstacle"]]
        mapping = {k: payment[k] for k in ("centers", "anchors", "orientation", "shift")}
        check_map(25, 14, obstacle, mapping, set(payment["sample_faces"]), 1)
    publish(output / "SEARCH-COMPLETE.json", {
        "verified": True, "N": 25, "B": 14, "native_exhaustive_search_terminated_successfully": True,
        "phase_sha256": sha(phase), "run_count": meta["run_count"], "rows_to_runs": meta["rows_to_runs"],
        "proof_prunes_not_type_count": meta["proof_prunes"], "union_not_yet_accepted": True,
        "global_optimality_proved": False,
    })
    folder = Path(str(target) + ".runs")
    paths = [folder / f"run-{i}.bin" for i in range(meta["run_count"])]
    assert (set(p.name for p in folder.iterdir()) if folder.exists() else set()) == {p.name for p in paths}
    final, union = finalize_runs(paths, meta, output / "bounded-finalization", fan_in=32)
    publish(output / "UNION-VERIFIED.json", union)
    unchanged(files)
    publish(output / "SUMMARY.json", {
        "verified": True, "N": 25, "B": 14, "complete_residual_family_search": True,
        "all_sorted_run_union_equality_verified": True, "residual_orbits": union["residual_orbits"],
        "catalog_absolute_path": str(final), "catalog_sha256": sha(final),
        "all_residual_lower_bounds_paid": union["residual_orbits"] == 0,
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    })
    print("N25/B14 complete residual catalogue:", union["residual_orbits"], "remaining types; not all-n25 proof", flush=True)


if __name__ == "__main__":
    main()
