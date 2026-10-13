"""New-file-only mechanical B15 lifecycle/driver adaptation; no signal sent."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish

assert __debug__


def derive_counted(source, target, changes):
    before_path, after_path = ROOT / source, ROOT / target
    assert not after_path.exists()
    original = before_path.read_text(encoding="utf8")
    text, counts = original, []
    for before, after in changes:
        count = text.count(before)
        assert count > 0, (source, before)
        counts.append(count)
        text = text.replace(before, after)
    reverse = text
    for (before, after), count in reversed(list(zip(changes, counts, strict=True))):
        assert reverse.count(after) == count, (source, after)
        reverse = reverse.replace(after, before)
    assert reverse == original
    after_path.write_text(text, encoding="utf8", newline="\n")
    return {
        "source": source, "source_sha256": sha(before_path),
        "target": target, "target_sha256": sha(after_path),
        "changes": changes, "occurrence_counts": counts, "exact_inverse_equals_frozen_source": True,
    }


def main():
    report_path = ROOT / "b15-degree-replacement-source-derivation.json"
    assert not report_path.exists()
    stop = derive_counted("b15_controlled_stop.py", "b15_degree_controlled_stop.py", [
        ('RECORD_NAME = "n25-B15-controlled-origin-replacement-20261005-v1"',
         'RECORD_NAME = "n25-B15-controlled-degree-replacement-20261005-v1"'),
        ("n25-B15-streamed-eight-sparse-search-20261005-v1",
         "n25-B15-origin-streamed-search-reboot-20261005-v1"),
        ("peel_streamed_collar-linux", "peel_origin_streamed_collar-linux"),
        ('    assert expected[-2:] == ["4058615", "100000"]',
         '    assert len(expected) == 15 and expected[-3:] == ["4058615", "100000", "1"]'),
        ('    checked = inspect_owned(previous)',
         '    from pending_degree_production_gate import production_gate\n'
         '    files.update(production_gate(\n'
         '        ROOT / "n25-B15-offline-contracted-union27-library-20261005-v1/LIBRARY.json",\n'
         '        ROOT / "n25-B15-union27-sparse-map-controls-20261005-v1/VERIFIED.json",\n'
         '        ROOT / "n25-B15-union27-eight-sparse-guard-controls-20261005-v1/VERIFIED.json", 15))\n'
         '    checked = inspect_owned(previous)'),
        ('"reason": "controlled performance replacement after exact B15 origin controls",',
         '"reason": "controlled earlier-degree replacement after full B15 degree and origin controls",\n'
         '        "degree_controls_sha256": sha(ROOT / "n25-pending-degree-upper-full-controls-20261005-v1/VERIFIED.json"),\n'
         '        "new_driver_derivation_sha256": sha(ROOT / "b15-degree-replacement-source-derivation.json"),'),
        ('Exact owned B15 native signalled for verified origin replacement:',
         'Exact owned reboot B15 native signalled for verified degree replacement:'),
    ])
    driver = derive_counted("run_reboot_origin_search.py", "run_b15_degree_origin_replacement.py", [
        ('from reboot_interruption_gate import recovery_gate',
         'from b15_degree_replacement_gate import b15_degree_replacement_gate as recovery_gate'),
        ('    maps, eight, guard = map(read, (args.maps, args.eight_controls, args.guard_controls))',
         '    maps, eight, guard = map(read, (args.maps, args.eight_controls, args.guard_controls))\n'
         '    from pending_degree_production_gate import production_gate\n'
         '    files.update(production_gate(args.library.resolve(), args.maps.resolve(),\n'
         '                                 args.guard_controls.resolve(), B))'),
        ('    assert B in (15, 16, 17), "only authoritatively reboot-interrupted N25 jobs are recovered"',
         '    assert B == 15, "only the identity-checked current B15 job is replaced"'),
        ('        "./peel_origin_streamed_collar-linux", "25", str(B), relative(target),',
         '        "./peel_pending_degree_origin_collar-linux", "25", str(B), relative(target),'),
        ('        "0", "dfs", "-", relative(table), str(CAP8), "100000", "1",',
         '        "0", "dfs", "-", relative(table), str(CAP8), "100000", "1", "1",'),
        ('"binary_linux_path": linux_path(ROOT / "peel_origin_streamed_collar-linux"),',
         '"binary_linux_path": linux_path(ROOT / "peel_pending_degree_origin_collar-linux"),'),
        ('"native_binary_sha256": sha(ROOT / "peel_origin_streamed_collar-linux"),',
         '"native_binary_sha256": sha(ROOT / "peel_pending_degree_origin_collar-linux"),'),
        ('    union = merge(target, code, output / "UNION")',
         '    assert header["pending_degree_upper_screen"]\n'
         '    assert header["pending_degree_upper_queries"] >= header["pending_degree_upper_prunes_not_type_count"]\n'
         '    union = merge(target, code, output / "UNION")'),
    ])
    publish(report_path, {
        "verified": True, "schema": "isolated-B15-degree-replacement-derivation-v1",
        "files": [stop, driver], "source_sha256": sha(Path(__file__)),
        "production_gate_sha256": sha(ROOT / "pending_degree_production_gate.py"),
        "lifecycle_gate_sha256": sha(ROOT / "b15_degree_replacement_gate.py"),
        "old_identity_and_nonzero_observed_terminal_and_duplicate_job_checks_retained": True,
        "original_exact_library_angle_storage_origin_and_final_union_checks_retained": True,
        "only_current_reboot_B15_target_and_verified_new_degree_gate_and_binary_changed": True,
        "all_old_sources_evidence_and_running_jobs_unchanged": True,
        "no_stop_signal_or_production_launch_performed": True, "global_optimality_proved": False,
    })
    print("B15 current-job degree lifecycle/driver isolated; no signal or launch", flush=True)


if __name__ == "__main__":
    main()
