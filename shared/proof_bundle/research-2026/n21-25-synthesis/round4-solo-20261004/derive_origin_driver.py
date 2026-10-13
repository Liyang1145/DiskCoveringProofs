"""Preserve all frozen math/storage gates, replace only terminal-failed B16/B17."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    original = ROOT / "run_streamed_eight_search.py"
    target, reportpath = ROOT / "run_origin_streamed_search.py", ROOT / "origin-driver-source-derivation.json"
    assert not target.exists() and not reportpath.exists()
    text = original.read_text(encoding="utf8")
    changes = [
        ("from merge_collar_chunks import merge", "from merge_origin_collar_chunks import merge\nfrom origin_production_gate import origin_gate"),
        ('    ap.add_argument("--storage-controls", type=Path, required=True)',
         '    ap.add_argument("--origin-controls", type=Path, required=True)\n'
         '    ap.add_argument("--failed-search", type=Path, required=True)\n'
         '    ap.add_argument("--storage-controls", type=Path, required=True)'),
        ('    assert B == 15, "only the failed B15 run is replaced by streamed storage"',
         '    assert B in (16, 17), "only the terminal-failed B16/B17 runs are replaced"\n'
         '    files.update(origin_gate(args.origin_controls.resolve(), args.failed_search.resolve(), B))'),
        ('f"N25-B{B}-complete-sorted-chunks.json"', 'f"N25-B{B}-complete-origin-sorted-chunks.json"'),
        ('"./peel_streamed_collar-linux", "25", str(B), relative(target)',
         '"./peel_origin_streamed_collar-linux", "25", str(B), relative(target)'),
        ('"0", "dfs", "-", relative(table), str(CAP8), "100000",',
         '"0", "dfs", "-", relative(table), str(CAP8), "100000", "1",'),
        ('rf"STREAMED COLLAR NATIVE PID=(\\d+) N=25 B={B}"',
         'rf"COVER ORIGIN NATIVE PID=(\\d+) N=25 B={B}"'),
        ('"binary_linux_path": linux_path(ROOT / "peel_streamed_collar-linux"),',
         '"binary_linux_path": linux_path(ROOT / "peel_origin_streamed_collar-linux"),'),
        ('"native_binary_sha256": sha(ROOT / "peel_streamed_collar-linux"),',
         '"native_binary_sha256": sha(ROOT / "peel_origin_streamed_collar-linux"),'),
        ('    assert header["schema"] == "complete-outer-collar-sorted-chunks-v1"',
         '    assert header["schema"] == "complete-cover-origin-collar-sorted-chunks-v1"\n'
         '    assert header["origin_cover_screen"] and header["origin_cover_only_N25"]\n'
         '    assert header["origin_cover_scope"] == "actual arbitrary disk covers only; not weak graph geometry"\n'
         '    assert not header.get("seeded_fixed_collar_restriction", False)'),
        ('        "full_triangulations_not_enumerated": True,\n',
         '        "full_triangulations_not_enumerated": True,\n'
         '        "actual_arbitrary_cover_origin_condition_used": True,\n'
         '        "not_a_complete_unqualified_geometric_weak_graph_catalog": True,\n'),
        ('    unchanged(files)\n    output.mkdir()',
         '    for path in (\n'
         '        ROOT / "peel_origin_streamed_collar.cpp", ROOT / "peel_origin_streamed_collar-linux",\n'
         '        ROOT / "cover_origin_obstruction.inc", ROOT / "merge_origin_collar_chunks.py",\n'
         '        ROOT / "derive_origin_streamed_collar.py", ROOT / "derive_origin_chunk_merge.py",\n'
         '        ROOT / "origin-streamed-collar-source-derivation.json", ROOT / "origin-chunk-merge-source-derivation.json",\n'
         '        ROOT / "origin_production_gate.py", ROOT / "test_origin_collar.py",\n'
         '        ROOT / "derive_origin_driver.py", ROOT / "origin-driver-source-derivation.json",\n'
         '        ROOT / "UNEXPOSED-ORIGIN-CENTER-SOURCE.md", args.origin_controls,\n'
         '    ):\n'
         '        bind(files, path)\n'
         '    unchanged(files)\n    output.mkdir()'),
    ]
    counts = []
    for before, after in changes:
        count = text.count(before)
        assert count == (2 if before.startswith('rf"STREAMED') else 1), (before, count)
        counts.append(count)
        text = text.replace(before, after)
    target.write_text(text, encoding="utf8", newline="\n")
    reportpath.write_text(json.dumps({
        "verified_mechanical_derivation": True,
        "original_source_sha256": sha(original), "derived_source_sha256": sha(target),
        "source_sha256": sha(Path(__file__)), "changes": changes, "occurrence_counts": counts,
        "original_library_angle_injection_partition_storage_gates_preserved": True,
        "new_origin_controls_and_confirmed_failure_absence_gate_added": True,
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
