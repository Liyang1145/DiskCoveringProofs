"""Complete small-case equality and timing experiment; no production approval."""
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    derivation_path = ROOT / "exact-state-reuse-source-derivation.json"
    derivation = read(derivation_path)
    assert derivation["verified"]
    assert derivation["source_sha256"] == sha(ROOT / "derive_exact_state_reuse.py")
    assert derivation["state_reuse_provider_sha256"] == sha(ROOT / "exact_collar_state_reuse.inc")
    assert derivation["source_induction_sha256"] == sha(ROOT / "EXACT-COLLAR-STATE-REUSE-SOURCE.md")
    record = derivation["file"]
    original = ROOT / record["source"]
    target = ROOT / record["target"]
    assert sha(original) == record["source_sha256"] and sha(target) == record["target_sha256"]
    text = original.read_text(encoding="utf8")
    for before, after in record["changes"]:
        assert text.count(before) == 1
        text = text.replace(before, after)
    assert text == target.read_text(encoding="utf8")
    library_path = ROOT / "n25-B15-offline-contracted-union27-library-20261005-v1/LIBRARY.json"
    constants, library, table, files = sparse_library_gate(library_path)
    reference_path = ROOT / "n25-B15-union27-eight-sparse-guard-controls-20261005-v1/N21-B15-eight-sparse-dfs.json"
    reference_report = read(reference_path.parent / "VERIFIED.json")
    assert reference_report["verified"]
    assert reference_report["library_sha256"] == sha(library_path)
    _, expected = collar_codes(reference_path, 21, 15)
    output.mkdir()
    cases, sets = [], []
    for flag in (0, 1):
        directory = output / f"flag-{flag}"
        directory.mkdir()
        manifest_path = directory / "MANIFEST.json"
        code, seconds = native_logged("peel_exact_state_origin_collar-linux", [
            21, 15, relative(manifest_path), constants["angle_scale"], *constants["angle_caps"],
            0, "dfs", "-", relative(table), 4058615, 100000, 1, flag,
        ], directory)
        assert code == 0
        manifest = read(manifest_path)
        assert manifest["exact_completed_state_reuse"] == bool(flag)
        assert manifest["exact_state_reuse_allocation_failures"] == 0
        assert manifest["exact_state_reuse_peak_words"] <= 4194304
        union = merge(manifest_path, 0, directory / "UNION")
        _, actual = codes_from_union(directory / "UNION/CATALOG.jsonl")
        assert actual == expected
        sets.append(actual)
        cases.append({
            "N": 21, "B": 15, "flag": flag, "actual_exit_code": code, "seconds": seconds,
            "calls": manifest["calls"], "weak_graphs": len(actual),
            "exact_reused_completed_states_not_types": manifest["exact_completed_state_reuse_hits_not_type_count"],
            "maximum_cached_words": manifest["exact_state_reuse_peak_words"],
            "full_union_matches_frozen_original_reference": True,
        })
        for path in (manifest_path, directory / "NATIVE-TERMINAL.json", directory / "UNION/VERIFIED.json",
                     directory / "UNION/CATALOG.jsonl"):
            bind(files, path)
        print("Exact state reuse full experiment:", flag, manifest["calls"],
              "calls;", manifest["exact_completed_state_reuse_hits_not_type_count"],
              "duplicate completed states;", round(seconds, 3), "seconds; set equal", flush=True)
    assert sets[0] == sets[1]
    for path in (Path(__file__), derivation_path, original, target, library_path, reference_path,
                 ROOT / "peel_exact_state_origin_collar-linux", ROOT / "exact_collar_state_reuse.inc",
                 ROOT / "EXACT-COLLAR-STATE-REUSE-SOURCE.md"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "EXPERIMENT.json", {
        "schema": "exact-completed-state-reuse-small-complete-experiment-v1",
        "complete_small_sets_equal": True, "cases": cases,
        "not_full_production_controls_or_approval": True,
        "additional_hash_collision_exception_and_complete_family_controls_required": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
