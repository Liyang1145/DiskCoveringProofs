"""Reaccept origin controls and confirmed old failures before a fresh replacement."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import read, bind, unchanged
from test_origin_collar import derivation_gate, codes_from_union
from test_outer_collar import WSL

assert __debug__


def b15_origin_controls_gate(controlspath):
    derivation_gate()
    driver = read(ROOT / "origin-driver-source-derivation.json")
    assert driver["verified_mechanical_derivation"]
    assert driver["original_source_sha256"] == sha(ROOT / "run_streamed_eight_search.py")
    assert driver["derived_source_sha256"] == sha(ROOT / "run_origin_streamed_search.py")
    assert driver["source_sha256"] == sha(ROOT / "derive_origin_driver.py")
    text = (ROOT / "run_streamed_eight_search.py").read_text(encoding="utf8")
    for (before, after), count in zip(driver["changes"], driver["occurrence_counts"], strict=True):
        assert text.count(before) == count
        text = text.replace(before, after)
    assert text == (ROOT / "run_origin_streamed_search.py").read_text(encoding="utf8")
    report = read(controlspath)
    assert report["verified"] and report["schema"] == "actual-cover-origin-streamed-enumeration-controls-v1"
    assert report["source_sha256"] == sha(ROOT / "test_origin_collar.py")
    assert report["native_source_sha256"] == sha(ROOT / "peel_origin_streamed_collar.cpp")
    assert report["native_binary_sha256"] == sha(ROOT / "peel_origin_streamed_collar-linux")
    assert report["origin_guard_sha256"] == sha(ROOT / "cover_origin_obstruction.inc")
    assert report["merge_source_sha256"] == sha(ROOT / "merge_origin_collar_chunks.py")
    assert report["all_native_exposed_masks_match_independent_face_unions"]
    assert report["graph_requests"] == 576 and report["native_origin_obstructions"] > 0
    assert report["all_32_dihedral_attaining_controls_retained"]
    assert len(report["complete_small_family_controls"]) == 8
    assert len(report["complete_restricted_N25_seed_controls"]) == 6
    assert report["complete_N25_other_B_control"]["complete_empty_by_origin_obstruction"]
    assert set(report["negative_controls_rejected"]) == {
        "bad-flag", "node-limit", "bad-N", "bad-B", "nonzero-exit", "prefix-manifest"}
    files = dict(report["files_relative_to_workspace"])
    unchanged(files)
    for row in report["complete_small_family_controls"]:
        name = f"N{row['N']}-{row['mode']}-sparse{int(row['sparse'])}-origin{row['flag']}"
        case = controlspath.parent / name
        manifestpath, terminalpath, unionpath = case / "MANIFEST.json", case / "NATIVE-TERMINAL.json", case / "UNION/VERIFIED.json"
        manifest, terminal, union = map(read, (manifestpath, terminalpath, unionpath))
        assert row["manifest_sha256"] == sha(manifestpath) == terminal["manifest_sha256"]
        assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] == 0
        assert row["union_sha256"] == sha(unionpath)
        assert union["verified"] and union["actual_native_exit_code"] == 0
        assert union["native_manifest_sha256"] == sha(manifestpath)
        assert union["complete_streaming_set_union"] and union["all_rows_ordered_and_canonical_checked"]
        assert union["source_sha256"] == sha(ROOT / "merge_origin_collar_chunks.py")
        for chunk in union["input_chunks"]:
            bindpath = manifestpath.with_name(chunk["file"])
            assert sha(bindpath) == chunk["sha256"]
            bind(files, bindpath)
        catalogpath = case / "UNION/CATALOG.jsonl"
        assert sha(catalogpath) == union["catalog_sha256"]
        _, actual = codes_from_union(catalogpath)
        assert len(actual) == row["weak_graphs"]
        for path in (manifestpath, terminalpath, unionpath, catalogpath):
            bind(files, path)
    for row in report["complete_restricted_N25_seed_controls"]:
        index = next(i for i in range(3) if i == row["seed"])
        case = controlspath.parent / f"N25-seed{index}-allocation0-origin{row['flag']}"
        terminal, manifest, union = map(read, (case / "NATIVE-TERMINAL.json", case / "MANIFEST.json",
                                             case / "UNION/VERIFIED.json"))
        assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] == 0
        assert row["manifest_sha256"] == sha(case / "MANIFEST.json") == terminal["manifest_sha256"]
        assert row["union_sha256"] == sha(case / "UNION/VERIFIED.json")
        assert manifest["seeded_fixed_collar_restriction"] and manifest["not_a_complete_boundary_family"]
        assert union["verified"] and union["actual_native_exit_code"] == 0
        assert union["complete_streaming_set_union"] and union["all_rows_ordered_and_canonical_checked"]
        assert union["unique_necessary_weak_graphs"] == (0 if row["centers"] == 25 and row["flag"] == "1" else 1)
        for path in (case / "MANIFEST.json", case / "NATIVE-TERMINAL.json", case / "UNION/VERIFIED.json"):
            bind(files, path)
    return files


def b15_replacement_gate(controlspath, previous, B):
    assert B == 15
    files = b15_origin_controls_gate(controlspath)
    from b15_controlled_stop import replacement_readiness
    files.update(replacement_readiness(previous))
    specific = read(ROOT / "n25-B15-origin-replacement-controls-20261005-v1/VERIFIED.json")
    assert specific["verified"] and specific["schema"] == "B15-origin-replacement-controls-v1"
    assert specific["source_sha256"] == sha(ROOT / "test_b15_origin_replacement.py")
    assert specific["origin_controls_sha256"] == sha(controlspath)
    assert specific["all_complete_B15_small_sets_equal"] and specific["all_N25_seed_results_paid_or_retained"]
    unchanged(specific["files_relative_to_workspace"])
    files.update(specific["files_relative_to_workspace"])
    report = read(ROOT / "b15-origin-replacement-source-derivation.json")
    assert report["source_sha256"] == sha(ROOT / "derive_b15_origin_replacement.py")
    assert report["gate_sha256"] == sha(Path(__file__))
    assert report["driver_sha256"] == sha(ROOT / "run_b15_origin_replacement.py")
    original = (ROOT / "run_origin_streamed_search.py").read_text(encoding="utf8")
    for before, after in report["driver_changes"]:
        assert original.count(before) == 1
        original = original.replace(before, after)
    assert original == (ROOT / "run_b15_origin_replacement.py").read_text(encoding="utf8")
    for path in (Path(__file__), ROOT / "b15_controlled_stop.py",
                 ROOT / "derive_b15_origin_replacement.py", ROOT / "b15-origin-replacement-source-derivation.json",
                 ROOT / "n25-B15-origin-replacement-controls-20261005-v1/VERIFIED.json"):
        bind(files, path)
    unchanged(files)
    return files
