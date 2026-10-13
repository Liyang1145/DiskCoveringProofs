"""Complete small-family equality and timing; not production approval."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from family_sparse_gate import sparse_library_gate
from test_cached_support_origin_partition import native_logged
from test_origin_collar import relative
from test_outer_collar import collar_codes
from test_streamed_collar import codes_from_union
from merge_origin_collar_chunks import merge

assert __debug__


def derivation_gate():
    path = ROOT / "pending-degree-upper-source-derivation.json"
    derivation = read(path)
    assert derivation["verified"]
    for key, filename in (
        ("source_sha256", "derive_pending_degree_upper.py"),
        ("provider_sha256", "pending_degree_upper.inc"),
        ("source_induction_sha256", "PENDING-DEGREE-UPPER-SOURCE.md"),
    ):
        assert derivation[key] == sha(ROOT / filename)
    record = derivation["file"]
    original, target = ROOT / record["source"], ROOT / record["target"]
    assert sha(original) == record["source_sha256"]
    assert sha(target) == record["target_sha256"]
    text = original.read_text(encoding="utf8")
    for before, after in record["changes"]:
        assert text.count(before) == 1
        text = text.replace(before, after)
    assert text == target.read_text(encoding="utf8")
    return path, original, target


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    derivation_path, original, target = derivation_gate()
    library_path = ROOT / "n25-B15-offline-contracted-union27-library-20261005-v1/LIBRARY.json"
    constants, library, table, files = sparse_library_gate(library_path)
    reference_root = ROOT / "n25-B15-union27-eight-sparse-guard-controls-20261005-v1"
    reference_report = read(reference_root / "VERIFIED.json")
    assert reference_report["verified"] and reference_report["library_sha256"] == sha(library_path)
    unchanged(reference_report["files_relative_to_workspace"])
    output.mkdir()
    cases = []
    for N in (21, 22):
        reference_path = reference_root / f"N{N}-B15-eight-sparse-dfs.json"
        _, expected = collar_codes(reference_path, N, 15)
        declared = next(row for row in reference_report["cases"] if row["N"] == N and row["mode"] == "dfs")
        assert sha(reference_path) == declared["residual_sha256"]
        sets = []
        for flag in (0, 1):
            directory = output / f"N{N}-flag-{flag}"
            directory.mkdir()
            manifest_path = directory / "MANIFEST.json"
            code, seconds = native_logged("peel_pending_degree_origin_collar-linux", [
                N, 15, relative(manifest_path), constants["angle_scale"], *constants["angle_caps"],
                0, "dfs", "-", relative(table), 4058615, 100000, 1, flag,
            ], directory)
            assert code == 0
            manifest = read(manifest_path)
            assert manifest["pending_degree_upper_screen"] == bool(flag)
            merge(manifest_path, code, directory / "UNION")
            _, actual = codes_from_union(directory / "UNION/CATALOG.jsonl")
            assert actual == expected
            sets.append(actual)
            cases.append({
                "N": N, "B": 15, "flag": flag, "actual_exit_code": code,
                "seconds": seconds, "calls": manifest["calls"], "weak_graphs": len(actual),
                "earlier_degree_prunes_not_type_count": manifest["pending_degree_upper_prunes_not_type_count"],
                "full_union_matches_frozen_original_reference": True,
            })
            for path in (manifest_path, directory / "NATIVE-TERMINAL.json",
                         directory / "UNION/VERIFIED.json", directory / "UNION/CATALOG.jsonl"):
                bind(files, path)
            print("Pending degree complete experiment:", N, flag, manifest["calls"], "calls;",
                  round(seconds, 3), "seconds; full set equal", flush=True)
        assert sets[0] == sets[1]
        bind(files, reference_path)
    for path in (Path(__file__), derivation_path, original, target, library_path,
                 reference_root / "VERIFIED.json", ROOT / "pending_degree_upper.inc",
                 ROOT / "PENDING-DEGREE-UPPER-SOURCE.md", ROOT / "peel_pending_degree_origin_collar-linux"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "EXPERIMENT.json", {
        "schema": "pending-degree-upper-small-complete-experiment-v1",
        "complete_small_sets_equal": True, "cases": cases,
        "not_full_production_controls_or_approval": True,
        "additional_direct_boundary_cases_audit_order_and_attaining_controls_required": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
