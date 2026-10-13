"""Join fresh N22 controls with actual completed N23 controls; no flag-only acceptance."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from cached_support_gate import derivation_gate
from family_sparse_gate import sparse_library_gate
from test_outer_collar import collar_codes
from test_streamed_collar import codes_from_union

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N22", type=Path, required=True)
    ap.add_argument("--N23", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    for key in vars(args):
        path = getattr(args, key).resolve()
        assert path.is_relative_to(ROOT)
        setattr(args, key, path)
    assert not args.output.exists()
    n22, n23 = read(args.N22), read(args.N23)
    assert n22["verified"] and n22["schema"] == "fresh-completed-N22-cached-origin-partition-controls-v1"
    assert n22["source_sha256"] == sha(ROOT / "audit_completed_N22_cached_controls.py")
    assert n22["both_native_exit_zero_results_rechecked"] and n22["both_complete_residual_sets_equal"]
    assert n22["all_482_difference_maps_fresh_checked_against_exact_strict_library"]
    assert n23["verified"] and n23["schema"] == "cached-support-origin-N23-partition-controls-v1"
    assert n23["source_sha256"] == sha(ROOT / "test_N23_cached_origin_partition.py")
    assert n23["all_two_complete_N23_partitions_paid"]
    assert n23["all_native_sparse_positive_samples_checked"]
    unchanged(n22["files_relative_to_workspace"]);unchanged(n23["files_relative_to_workspace"])
    files = derivation_gate()
    files.update(n22["files_relative_to_workspace"]);files.update(n23["files_relative_to_workspace"])
    library_path = ROOT / "n25-B16-offline-union-sparse-library-20261005-v1/LIBRARY.json"
    _, library, _, dependencies = sparse_library_gate(library_path)
    files.update(dependencies)
    assert n22["library_sha256"] == n23["library_sha256"] == sha(library_path)
    cases = []
    for N, report, directory in (
        (22, n22, ROOT / "n25-B16-cached-support-origin-partition-controls-20261005-v1"),
        (23, n23, args.N23.parent),
    ):
        assert {(row["N"], row["mode"]) for row in report["cases"]} == {(N, "dfs"), (N, "audit")}
        sets = []
        for row in report["cases"]:
            mode = row["mode"]
            case = directory / f"N{N}-{mode}"
            terminal = read(case / "NATIVE-TERMINAL.json")
            manifest = read(case / "MANIFEST.json")
            union = read(case / "UNION/VERIFIED.json")
            assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] == 0
            assert row["manifest_sha256"] == union["native_manifest_sha256"] == sha(case / "MANIFEST.json")
            assert row["union_sha256"] == sha(case / "UNION/VERIFIED.json")
            assert union["verified"] and union["actual_native_exit_code"] == 0
            assert union["complete_streaming_set_union"] and union["all_rows_ordered_and_canonical_checked"]
            assert union["source_sha256"] == sha(ROOT / "merge_origin_collar_chunks.py")
            assert manifest["mode"] == mode and manifest["N"] == N and manifest["B"] == 16
            assert manifest["origin_cover_prunes_not_type_count"] == 0
            assert manifest["sparse_patterns_loaded"] == sum(o["centers"] <= N for o in library["obstacles"])
            catalog_path = case / "UNION/CATALOG.jsonl"
            assert sha(catalog_path) == union["catalog_sha256"]
            _, actual = codes_from_union(catalog_path)
            assert len(actual) == row["residual_weak_graphs"]
            sets.append(actual)
            cases.append(row)
        assert sets[0] == sets[1]
    for path in (Path(__file__), args.N22, args.N23, library_path,
                 ROOT / "N23-cached-partition-control-derivation.json"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(args.output, {
        "verified": True, "schema": "cached-support-origin-complete-partition-controls-v2",
        "N": 25, "B": 16, "cases": cases,
        "all_four_complete_small_family_partitions_paid": True,
        "both_dfs_audit_residual_sets_equal_for_each_order": True,
        "all_removed_graphs_individually_explicitly_strictly_paid": True,
        "actual_exit_zero_and_full_union_content_rechecked_for_every_case": True,
        "source_N22_report_sha256": sha(args.N22), "source_N23_report_sha256": sha(args.N23),
        "library_sha256": sha(library_path), "files_relative_to_workspace": files,
        "source_sha256": sha(Path(__file__)),
        "native_binary_sha256": sha(ROOT / "peel_cached_support_origin_collar-linux"),
        "not_a_complete_N25_boundary_family": True, "global_optimality_proved": False,
    })
    print("All four cached origin complete small-family partitions joined and reaccepted", flush=True)


if __name__ == "__main__":
    main()
