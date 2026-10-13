"""Check frozen tiny-slab controls and their actual terminal/artifact bindings."""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, bind
from test_streamed_collar import derivation_gate
from test_outer_collar import collar_codes

assert __debug__


def storage_gate(controlspath):
    derivation_gate()
    driver = read(ROOT / "streamed-driver-source-derivation.json")
    assert driver["verified_mechanical_derivation"]
    assert driver["original_source_sha256"] == sha(ROOT / "run_eight_rod_search.py")
    assert driver["derived_source_sha256"] == sha(ROOT / "run_streamed_eight_search.py")
    assert driver["source_sha256"] == sha(ROOT / "derive_streamed_driver.py")
    text = (ROOT / "run_eight_rod_search.py").read_text(encoding="utf8")
    for (before, after), count in zip(driver["changes"], driver["occurrence_counts"], strict=True):
        assert text.count(before) == count
        text = text.replace(before, after)
    assert text == (ROOT / "run_streamed_eight_search.py").read_text(encoding="utf8")
    report = read(controlspath)
    assert report["verified"] and report["schema"] == "streamed-collar-storage-controls-v1"
    for field, filename in (
        ("source_sha256", "test_streamed_collar.py"),
        ("native_source_sha256", "peel_streamed_collar.cpp"),
        ("native_binary_sha256", "peel_streamed_collar-linux"),
        ("storage_include_sha256", "collar_chunk_storage.inc"),
        ("merge_source_sha256", "merge_collar_chunks.py"),
        ("derivation_sha256", "streamed-collar-source-derivation.json"),
    ):
        assert report[field] == sha(ROOT / filename)
    assert report["all_complete_union_sets_equal_to_in_memory_references"]
    assert set(report["negative_controls_rejected"]) == {
        "node-limit-no-complete-manifest", "nonzero-exit-rejected", "missing-slab",
        "wrong-row-count", "prefix-manifest",
    }
    assert report["full_n25_search_not_run_by_this_control"]
    expected_cases = [(20, "dfs", 1, False), (21, "dfs", 7, False),
                      (21, "audit", 2, False), (21, "dfs", 1, True)]
    assert [(r["N"], r["mode"], r["slab_limit"], r["sparse_guard_enabled"])
            for r in report["cases"]] == expected_cases
    files = {}
    bind(files, controlspath)
    reference_dir = ROOT / "n25-B14-eight-sparse-guard-controls-20261005-v1"
    references = read(reference_dir / "VERIFIED.json")
    bind(files, reference_dir / "VERIFIED.json")
    for row in report["cases"]:
        N, mode, slab, sparse = (row[k] for k in ("N", "mode", "slab_limit", "sparse_guard_enabled"))
        case = controlspath.parent / f"N{N}-{mode}-slab{slab}-sparse{int(sparse)}"
        manifestpath, terminalpath = case / "MANIFEST.json", case / "NATIVE-TERMINAL.json"
        unionpath = case / "UNION/VERIFIED.json"
        manifest, terminal, union = map(read, (manifestpath, terminalpath, unionpath))
        assert row["manifest_sha256"] == terminal["manifest_sha256"] == sha(manifestpath)
        assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] == 0
        assert row["union_replay_sha256"] == sha(unionpath)
        assert union["verified"] and union["all_declared_slabs_fully_scanned"]
        assert union["all_rows_ordered_and_canonical_checked"] and union["complete_streaming_set_union"]
        assert union["native_manifest_sha256"] == sha(manifestpath)
        assert union["source_sha256"] == sha(ROOT / "merge_collar_chunks.py")
        assert union["actual_native_exit_code"] == 0
        assert union["unique_necessary_weak_graphs"] == row["unique_graphs"]
        assert union["cross_slab_duplicates_removed"] == row["cross_slab_duplicates_removed"]
        assert manifest["complete_necessary_outer_search"] and manifest["slab_limit"] == slab
        assert (manifest["N"], manifest["B"], manifest["mode"]) == (N, 14, mode)
        assert len(manifest["chunks"]) == len(union["input_chunks"]) == manifest["chunk_count"]
        for chunk, checked in zip(manifest["chunks"], union["input_chunks"], strict=True):
            path = (ROOT / chunk["file"]).resolve()
            assert path.is_relative_to(case.resolve()) and sha(path) == checked["sha256"]
            assert chunk["rows"] == checked["rows"]
            bind(files, path)
        catalogpath = case / "UNION" / union["catalog_file"]
        bindingspath = case / "UNION" / union["bindings_file"]
        assert sha(catalogpath) == union["catalog_sha256"]
        assert sha(bindingspath) == union["bindings_sha256"]
        actual = []
        with catalogpath.open(encoding="ascii") as stream:
            header = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
            assert header["N"] == N and header["B"] == 14
            for index, line in enumerate(stream):
                group = json.loads(line, object_pairs_hook=no_duplicate_keys)
                assert group["id"] == index
                actual.append(tuple(group["faces"]))
        assert len(actual) == row["unique_graphs"] and len(set(actual)) == len(actual)
        reference = reference_dir / (f"N{N}-B14-eight-" +
                                    ("sparse-dfs.json" if sparse else "baseline.json"))
        old = next(r for r in references["cases"] if r["N"] == N and r["mode"] == "dfs")
        assert sha(reference) == old["residual_sha256" if sparse else "baseline_sha256"]
        _, expected = collar_codes(reference, N, 14)
        assert set(actual) == expected
        for path in (manifestpath, terminalpath, unionpath, catalogpath, bindingspath, reference):
            bind(files, path)
    assert any(r["cross_slab_duplicates_removed"] > 0 for r in report["cases"])
    return files
