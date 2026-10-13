"""Fresh replay of both completed N22 controls, without rerunning enumeration."""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from group_catalog import validate
from n25_outer_search import read, publish, bind, unchanged
from cached_support_gate import derivation_gate
from family_sparse_gate import sparse_library_gate
from test_outer_collar import collar_codes
from test_streamed_collar import codes_from_union

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    files = derivation_gate()
    library_path = ROOT / "n25-B16-offline-union-sparse-library-20261005-v1/LIBRARY.json"
    constants, library, table, dependencies = sparse_library_gate(library_path)
    files.update(dependencies)
    by_id = {row["id"]: row for row in library["obstacles"]}
    prior = ROOT / "n25-B16-cached-support-origin-partition-controls-20261005-v1"
    baseline_path = ROOT / "n25-B16-eight-sparse-guard-controls-20261005-v1/N22-B16-eight-baseline.json"
    baseline, all_codes = collar_codes(baseline_path, 22, 16)
    assert len(all_codes) == 303
    centers = {tuple(row["faces"]): row["centers"] for row in baseline["weak_graphs"]}
    cases, residual_sets = [], []
    for mode in ("dfs", "audit"):
        directory = prior / f"N22-{mode}"
        manifest_path, terminal_path, union_path = (
            directory / filename for filename in ("MANIFEST.json", "NATIVE-TERMINAL.json", "UNION/VERIFIED.json"))
        manifest, terminal, union = map(read, (manifest_path, terminal_path, union_path))
        assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] == 0
        command = terminal["command"]
        assert command[7:10] == ["./peel_cached_support_origin_collar-linux", "22", "16"]
        assert command[-2:] == ["100000", "1"]
        assert command[16] == mode
        assert manifest["complete_necessary_outer_search"] and manifest["N"] == 22 and manifest["B"] == 16
        assert manifest["mode"] == mode
        assert manifest["sparse_patterns_loaded"] == sum(o["centers"] <= 22 for o in library["obstacles"])
        assert manifest["origin_cover_prunes_not_type_count"] == 0
        assert union["verified"] and union["native_manifest_sha256"] == sha(manifest_path)
        assert union["source_sha256"] == sha(ROOT / "merge_origin_collar_chunks.py")
        assert union["actual_native_exit_code"] == 0 and union["complete_streaming_set_union"]
        assert union["all_declared_slabs_fully_scanned"] and union["all_rows_ordered_and_canonical_checked"]
        catalog_path = directory / "UNION/CATALOG.jsonl"
        bindings_path = directory / "UNION/bindings.jsonl"
        assert sha(catalog_path) == union["catalog_sha256"] and sha(bindings_path) == union["bindings_sha256"]
        _, residual = codes_from_union(catalog_path)
        assert len(residual) == union["unique_necessary_weak_graphs"] == 62 and residual <= all_codes
        residual_sets.append(residual)
        removed = sorted(all_codes-residual)
        maps_path, requests_path = directory / "REMOVED-MAPS.json", directory / "REMOVED-REQUESTS.tsv"
        maps = read(maps_path)
        assert maps["scope"] == "sparse subgraph maps only" and len(maps["matches"]) == len(removed) == 241
        with requests_path.open(encoding="ascii") as stream:
            for index, (code, answer) in enumerate(zip(removed, maps["matches"], strict=True)):
                tokens = list(map(int, next(stream).split()))
                assert tokens == [index, len(code), *code]
                assert answer["request"] == index and answer["obstacle"] in by_id
                obstacle = by_id[answer["obstacle"]]
                mapping = {key: answer[key] for key in ("centers", "anchors", "orientation", "shift")}
                assert len(mapping["centers"]) == obstacle["centers"]
                validate(centers[code], 16, obstacle["faces"], mapping, code)
            assert not stream.read().strip()
        for payment in manifest["sparse_payments"]:
            obstacle = by_id[payment["obstacle"]]
            mapping = {key: payment[key] for key in ("centers", "anchors", "orientation", "shift")}
            validate(22, 16, obstacle["faces"], mapping, payment["sample_faces"])
        for chunk in union["input_chunks"]:
            path = directory / chunk["file"]
            assert sha(path) == chunk["sha256"]
            bind(files, path)
        for path in (manifest_path, terminal_path, union_path, catalog_path, bindings_path, maps_path,
                     requests_path, directory / "NATIVE-STDERR.log"):
            bind(files, path)
        assert terminal["native_log_sha256"] == sha(directory / "NATIVE-STDERR.log")
        cases.append({"N": 22, "B": 16, "mode": mode, "baseline_weak_graphs": 303,
                      "residual_weak_graphs": 62, "removed_graphs_explicitly_paid": 241,
                      "new_calls": manifest["calls"], "new_seconds": terminal["seconds"],
                      "manifest_sha256": sha(manifest_path), "union_sha256": sha(union_path)})
    assert residual_sets[0] == residual_sets[1]
    for path in (Path(__file__), baseline_path, library_path, ROOT / "test_cached_support_origin_partition.py",
                 ROOT / "peel_cached_support_origin_collar-linux", HIGH / "group_catalog.py"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output, {
        "verified": True, "schema": "fresh-completed-N22-cached-origin-partition-controls-v1",
        "N": 25, "B": 16, "cases": cases, "both_native_exit_zero_results_rechecked": True,
        "both_complete_residual_sets_equal": True,
        "all_482_difference_maps_fresh_checked_against_exact_strict_library": True,
        "no_enumeration_restarted_by_this_audit": True,
        "library_sha256": sha(library_path), "files_relative_to_workspace": files,
        "source_sha256": sha(Path(__file__)), "not_a_complete_N25_boundary_family": True,
        "global_optimality_proved": False,
    })
    print("Both completed N22 cached controls fresh accepted:",
          "303 -> 62; 482 difference maps; no search rerun", flush=True)


if __name__ == "__main__":
    main()
