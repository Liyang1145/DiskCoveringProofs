"""New production driver with cached necessary filters; original nonmatching gates retained."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import publish

assert __debug__


def main():
    source = ROOT / "run_reboot_origin_search.py"
    target = ROOT / "run_cached_reboot_origin_search.py"
    report_path = ROOT / "cached-reboot-origin-driver-source-derivation.json"
    assert not target.exists() and not report_path.exists()
    original = source.read_text(encoding="utf8")
    start = original.index('    assert maps["verified"]')
    end = original.index('    assert eight["verified"]', start)
    maps_block = original[start:end]
    start_guard = original.index('    assert guard["verified"]', end)
    end_guard = original.index('    assert B in (15, 16, 17)', start_guard)
    guard_block = original[start_guard:end_guard]
    changes = [
        (maps_block,
         "    from cached_origin_production_gate import production_gate\n"
         "    files.update(production_gate(args.library.resolve(), args.maps.resolve(),\n"
         "                                 args.guard_controls.resolve(), B))\n"),
        (guard_block, "    assert B == 16, \"only the reboot-interrupted B16 search uses this new version\"\n"),
        ('"./peel_origin_streamed_collar-linux", "25", str(B), relative(target)',
         '"./peel_cached_support_origin_collar-linux", "25", str(B), relative(target)'),
        ('linux_path(ROOT / "peel_origin_streamed_collar-linux")',
         'linux_path(ROOT / "peel_cached_support_origin_collar-linux")'),
        ('"native_binary_sha256": sha(ROOT / "peel_origin_streamed_collar-linux")',
         '"native_binary_sha256": sha(ROOT / "peel_cached_support_origin_collar-linux")'),
    ]
    text, counts = original, []
    for before, after in changes:
        count = text.count(before)
        assert count == 1
        counts.append(count)
        text = text.replace(before, after)
    reverse = text
    for before, after in reversed(changes):
        assert reverse.count(after) == 1
        reverse = reverse.replace(after, before)
    assert reverse == original
    target.write_text(text, encoding="utf8", newline="\n")
    publish(report_path, {
        "verified": True, "schema": "cached-reboot-origin-driver-isolated-derivation-v1",
        "original_source_sha256": sha(source), "derived_source_sha256": sha(target),
        "changes": changes, "occurrence_counts": counts, "exact_inverse_equals_original": True,
        "all_original_exact_library_angle_storage_origin_lifecycle_and_final_union_checks_retained": True,
        "old_matching_controls_replaced_by_stronger_cached_matching_controls_not_bypassed": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
