"""Preserve the frozen production mathematics gates, change only storage."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source = ROOT / "run_eight_rod_search.py"
    target = ROOT / "run_streamed_eight_search.py"
    reportpath = ROOT / "streamed-driver-source-derivation.json"
    assert not target.exists() and not reportpath.exists()
    old = source.read_text(encoding="utf8")
    changes = [
        ("from test_outer_collar import collar_codes, linux_path, WSL",
         "from test_outer_collar import linux_path, WSL\n"
         "from streamed_storage_gate import storage_gate\n"
         "from merge_collar_chunks import merge"),
        ('    ap.add_argument("--output", type=Path, required=True)',
         '    ap.add_argument("--storage-controls", type=Path, required=True)\n'
         '    ap.add_argument("--output", type=Path, required=True)'),
        ('    files.update(maps["files_relative_to_workspace"])',
         '    assert B == 15, "only the failed B15 run is replaced by streamed storage"\n'
         '    files.update(storage_gate(args.storage_controls.resolve()))\n'
         '    files.update(maps["files_relative_to_workspace"])'),
        ('    unchanged(files)\n    output.mkdir()',
         '    for path in (\n'
         '        ROOT / "run_eight_rod_search.py", ROOT / "derive_streamed_driver.py",\n'
         '        ROOT / "streamed-driver-source-derivation.json", ROOT / "streamed_storage_gate.py",\n'
         '        ROOT / "test_streamed_collar.py", ROOT / "derive_streamed_collar.py",\n'
         '        ROOT / "streamed-collar-source-derivation.json", ROOT / "collar_chunk_storage.inc",\n'
         '        ROOT / "peel_streamed_collar.cpp", ROOT / "peel_streamed_collar-linux",\n'
         '        ROOT / "merge_collar_chunks.py", args.storage_controls,\n'
         '    ):\n'
         '        bind(files, path)\n'
         '    unchanged(files)\n    output.mkdir()'),
        ('f"N25-B{B}-necessary-eight-rod-collars.json"', 'f"N25-B{B}-complete-sorted-chunks.json"'),
        ('"./peel_eight_rod_collar-linux", "25", str(B), relative(target)',
         '"./peel_streamed_collar-linux", "25", str(B), relative(target)'),
        ('"0", "dfs", "-", relative(table), str(CAP8),',
         '"0", "dfs", "-", relative(table), str(CAP8), "100000",'),
        ('"cap8": CAP8, "same_non_omitted_recursion_and_sparse_injection_checks": True,',
         '"cap8": CAP8, "same_non_omitted_recursion_and_sparse_injection_checks": True,\n'
         '        "slab_limit": 100000, "storage_never_used_for_recursion_pruning": True,'),
        ('rf"EIGHT ROD NATIVE PID=(\\d+) N=25 B={B}"',
         'rf"STREAMED COLLAR NATIVE PID=(\\d+) N=25 B={B}"'),
        ('"binary_linux_path": linux_path(ROOT / "peel_eight_rod_collar-linux"),',
         '"binary_linux_path": linux_path(ROOT / "peel_streamed_collar-linux"),'),
        ('"native_binary_sha256": sha(ROOT / "peel_eight_rod_collar-linux"),',
         '"native_binary_sha256": sha(ROOT / "peel_streamed_collar-linux"),'),
        ('"native_log_sha256": sha(output / "NATIVE-STDERR.log"), "global_optimality_proved": False,',
         '"native_log_sha256": sha(output / "NATIVE-STDERR.log"),\n'
         '        "manifest_sha256": sha(target) if target.exists() else None,\n'
         '        "global_optimality_proved": False,'),
        ('    header, codes = collar_codes(target, 25, B)', '    header = read(target)'),
    ]
    start = old.index('    groups = [{"id": gid, **row, "members": 1}')
    end = old.index('\n\n\nif __name__ == "__main__":', start)
    changes.append((old[start:end], '''    assert header["schema"] == "complete-outer-collar-sorted-chunks-v1"
    assert header["complete_necessary_outer_search"] and not header["complete_full_triangulations"]
    assert header["N"] == 25 and header["B"] == B and header["slab_limit"] == 100000
    union = merge(target, code, output / "UNION")
    unchanged(files)
    publish(output / "SUMMARY.json", {
        "verified": True, "N": 25, "B": B,
        "complete_necessary_outer_collar_overapproximation": True,
        "unpaid_weak_graphs": union["unique_necessary_weak_graphs"],
        "all_remaining_weak_lower_bounds_paid": union["unique_necessary_weak_graphs"] == 0,
        "full_triangulations_not_enumerated": True,
        "source_induction_required_for_cover_transport": True,
        "cap8": CAP8, "native_manifest_sha256": sha(target),
        "complete_union_report_sha256": sha(output / "UNION/VERIFIED.json"),
        "catalog_sha256": union["catalog_sha256"],
        "payment_samples_explicitly_mapped": len(header["sparse_payments"]),
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    })
    print("N25/B", B, "complete streamed necessary union accepted:",
          union["unique_necessary_weak_graphs"], "unpaid weak graphs", flush=True)'''))
    text, counts = old, []
    for before, after in changes:
        count = text.count(before)
        assert count == (2 if before.startswith('rf"EIGHT ROD') else 1), (before, count)
        counts.append(count)
        text = text.replace(before, after)
    target.write_text(text, encoding="utf8", newline="\n")
    reportpath.write_text(json.dumps({
        "verified_mechanical_derivation": True,
        "original_source_sha256": sha(source), "derived_source_sha256": sha(target),
        "source_sha256": sha(Path(__file__)), "changes": changes, "occurrence_counts": counts,
        "original_mathematical_library_angle_mapping_partition_gates_preserved": True,
        "new_slab_control_gate_added": True, "actual_zero_exit_required": True,
        "only_failed_B15_replacement_allowed": True, "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
