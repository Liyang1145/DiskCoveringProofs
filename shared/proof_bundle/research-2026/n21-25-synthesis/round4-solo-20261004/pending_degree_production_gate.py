"""Fresh complete-set and source gates for the isolated B15 degree version."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, bind, unchanged
from cached_support_gate import derivation_gate as cached_derivation
from test_pending_degree_upper_small import derivation_gate as degree_derivation
from test_outer_collar import collar_codes
from test_streamed_collar import codes_from_union
from family_sparse_gate import sparse_library_gate

assert __debug__


def driver_derivation_gate():
    path = ROOT / "b15-degree-replacement-source-derivation.json"
    report = read(path)
    assert report["verified"] and report["schema"] == "isolated-B15-degree-replacement-derivation-v1"
    assert report["source_sha256"] == sha(ROOT / "derive_b15_degree_replacement.py")
    assert report["production_gate_sha256"] == sha(Path(__file__))
    assert report["lifecycle_gate_sha256"] == sha(ROOT / "b15_degree_replacement_gate.py")
    for record in report["files"]:
        original, target = ROOT / record["source"], ROOT / record["target"]
        assert sha(original) == record["source_sha256"] and sha(target) == record["target_sha256"]
        text = original.read_text(encoding="utf8")
        for (before, after), count in zip(record["changes"], record["occurrence_counts"], strict=True):
            assert text.count(before) == count
            text = text.replace(before, after)
        assert text == target.read_text(encoding="utf8")
        for (before, after), count in reversed(list(zip(record["changes"], record["occurrence_counts"], strict=True))):
            assert text.count(after) == count
            text = text.replace(after, before)
        assert text == original.read_text(encoding="utf8")
    return path


def production_gate(library_path, maps_path, guard_path, B):
    assert B == 15
    library_path, maps_path, guard_path = (path.resolve() for path in (library_path, maps_path, guard_path))
    assert library_path == ROOT / "n25-B15-offline-contracted-union27-library-20261005-v1/LIBRARY.json"
    constants, library, table, files = sparse_library_gate(library_path)
    assert library["B"] == B and library["obstacle_count"] == 27
    files.update(cached_derivation())
    degree_path, original, target = degree_derivation()
    driver_path = driver_derivation_gate()
    maps, guard = read(maps_path), read(guard_path)
    assert maps["verified"] and maps["library_sha256"] == guard["library_sha256"] == sha(library_path)
    assert maps["source_sha256"] == sha(ROOT / "verify_sparse_maps_fast.py")
    assert maps["matcher_binary_sha256"] == sha(ROOT / "sparse_outer_match-linux")
    assert maps["all_source_trees_fresh_exact_replayed"]
    assert guard["verified"] and guard["schema"] == "eight-rod-sparse-complete-partition-controls-v1"
    assert guard["source_sha256"] == sha(ROOT / "test_eight_sparse_guard.py")
    assert guard["maps_controls_sha256"] == sha(maps_path)
    assert guard["all_baseline_minus_residual_graphs_individually_paid"]
    assert {(row["N"], row["mode"]) for row in guard["cases"]} == {
        (21, "dfs"), (21, "audit"), (22, "dfs"), (22, "audit")}
    for report in (maps, guard):
        unchanged(report["files_relative_to_workspace"])
        files.update(report["files_relative_to_workspace"])
    experiment_path = ROOT / "n25-B15-pending-degree-upper-small-experiment-20261005-v1/EXPERIMENT.json"
    controls_path = ROOT / "n25-pending-degree-upper-full-controls-20261005-v1/VERIFIED.json"
    experiment, controls = read(experiment_path), read(controls_path)
    assert experiment["complete_small_sets_equal"]
    assert experiment["source_sha256"] == sha(ROOT / "test_pending_degree_upper_small.py")
    assert {(row["N"], row["flag"]) for row in experiment["cases"]} == {
        (21, 0), (21, 1), (22, 0), (22, 1)}
    assert controls["verified"] and controls["arithmetic_states_checked"] == 506
    assert controls["source_sha256"] == sha(ROOT / "test_pending_degree_upper_controls.py")
    assert controls["known_N25_attaining_seed_explicitly_retained"]
    assert set(controls["refusals"]) == {"invalid-flag", "incomplete-node-limit"}
    assert len(controls["fixed_N25_seed_cases"]) == 4
    assert {(row["N"], row["B"], row["mode"], row["flag"]) for row in controls["whole_set_cases"]} == {
        *((N, B, mode, flag) for N, B in ((7, 4), (8, 5))
          for mode in ("noscreen", "audit-noscreen") for flag in (0, 1)),
        (21, 15, "audit", 1), (22, 15, "audit", 1),
    }
    for report in (experiment, controls):
        unchanged(report["files_relative_to_workspace"])
        files.update(report["files_relative_to_workspace"])
    for N, mode in ((21, "dfs"), (22, "dfs"), (21, "audit"), (22, "audit")):
        reference_path = guard_path.parent / f"N{N}-B15-eight-sparse-{mode}.json"
        declared = next(row for row in guard["cases"] if (row["N"], row["mode"]) == (N, mode))
        assert sha(reference_path) == declared["residual_sha256"]
        _, expected = collar_codes(reference_path, N, B)
        directory = (experiment_path.parent / f"N{N}-flag-1" if mode == "dfs" else
                     controls_path.parent / f"N{N}-B15-audit-flag1")
        manifest_path, terminal_path, union_path, catalog_path = (
            directory / name for name in ("MANIFEST.json", "NATIVE-TERMINAL.json",
                                          "UNION/VERIFIED.json", "UNION/CATALOG.jsonl"))
        manifest, terminal, union = map(read, (manifest_path, terminal_path, union_path))
        assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] == 0
        assert manifest["N"] == N and manifest["B"] == B and manifest["mode"] == mode
        assert manifest["screen"] and manifest["eight_rod_screen"] and manifest["origin_cover_screen"]
        assert manifest["pending_degree_upper_screen"] and manifest["sparse_patterns_loaded"] == 27
        assert manifest["caps"] == constants["angle_caps"] and manifest["cap8"] == 4058615
        assert union["verified"] and union["actual_native_exit_code"] == 0
        assert union["native_manifest_sha256"] == sha(manifest_path)
        assert union["complete_streaming_set_union"] and union["all_rows_ordered_and_canonical_checked"]
        assert union["source_sha256"] == sha(ROOT / "merge_origin_collar_chunks.py")
        assert union["catalog_sha256"] == sha(catalog_path)
        _, actual = codes_from_union(catalog_path)
        assert actual == expected
        for path in (reference_path, manifest_path, terminal_path, union_path, catalog_path):
            bind(files, path)
    for path in (Path(__file__), library_path, table, maps_path, guard_path, degree_path, original, target,
                 driver_path, experiment_path, controls_path, ROOT / "pending_degree_upper.inc",
                 ROOT / "PENDING-DEGREE-UPPER-SOURCE.md", ROOT / "peel_pending_degree_origin_collar-linux",
                 ROOT / "derive_b15_degree_replacement.py", ROOT / "b15_degree_controlled_stop.py",
                 ROOT / "b15_degree_replacement_gate.py", ROOT / "run_b15_degree_origin_replacement.py"):
        bind(files, path)
    unchanged(files)
    return files
