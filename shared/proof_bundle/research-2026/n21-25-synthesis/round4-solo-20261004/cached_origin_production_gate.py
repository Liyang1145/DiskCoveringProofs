"""Strict-library, necessary-filter, complete partition and N25 seed gates."""
from pathlib import Path
from stream_catalog import sha
from n25_outer_search import read, bind, unchanged
from cached_support_gate import derivation_gate

ROOT = Path(__file__).resolve().parent
assert __debug__


def production_gate(library_path, maps_path, guard_path, B):
    assert B == 16
    files = derivation_gate()
    driver_report_path = ROOT / "cached-reboot-origin-driver-source-derivation.json"
    driver = read(driver_report_path)
    assert driver["verified"] and driver["schema"] == "cached-reboot-origin-driver-isolated-derivation-v1"
    assert driver["source_sha256"] == sha(ROOT / "derive_cached_reboot_origin_driver.py")
    assert driver["original_source_sha256"] == sha(ROOT / "run_reboot_origin_search.py")
    assert driver["derived_source_sha256"] == sha(ROOT / "run_cached_reboot_origin_search.py")
    assert driver["all_original_exact_library_angle_storage_origin_lifecycle_and_final_union_checks_retained"]
    assert driver["old_matching_controls_replaced_by_stronger_cached_matching_controls_not_bypassed"]
    text = (ROOT / "run_reboot_origin_search.py").read_text(encoding="utf8")
    for (before, after), count in zip(driver["changes"], driver["occurrence_counts"], strict=True):
        assert text.count(before) == count == 1
        text = text.replace(before, after)
    assert text == (ROOT / "run_cached_reboot_origin_search.py").read_text(encoding="utf8")
    maps, guard = read(maps_path), read(guard_path)
    assert maps["verified"] and maps["schema"] == "bounded-sparse-support-cache-map-controls-v1"
    assert maps["source_sha256"] == sha(ROOT / "test_cached_sparse_support.py")
    assert maps["library_sha256"] == guard["library_sha256"] == sha(library_path)
    assert maps["all_old_new_first_positive_maps_identical"]
    assert maps["all_positive_center_anchor_and_face_maps_checked"]
    assert maps["known_attaining_result_unchanged_from_frozen_control"]
    assert maps["native_binary_sha256"] == sha(ROOT / "sparse_support_cached_match-linux")
    assert set(maps["negative_controls_rejected"]) == {"bad-schema", "bad-id", "extra-column", "bad-N"}
    assert {row["requests"] for row in maps["cases"]} == {1507, 100000}
    assert all(row["all_old_new_answers_and_maps_equal"] for row in maps["cases"])
    assert guard["verified"] and guard["schema"] == "cached-support-origin-complete-partition-controls-v2"
    assert guard["source_sha256"] == sha(ROOT / "join_cached_origin_partition_controls.py")
    assert guard["all_four_complete_small_family_partitions_paid"]
    assert guard["both_dfs_audit_residual_sets_equal_for_each_order"]
    assert guard["all_removed_graphs_individually_explicitly_strictly_paid"]
    assert guard["actual_exit_zero_and_full_union_content_rechecked_for_every_case"]
    assert guard["native_binary_sha256"] == sha(ROOT / "peel_cached_support_origin_collar-linux")
    assert {(row["N"], row["mode"]) for row in guard["cases"]} == {
        (22, "dfs"), (22, "audit"), (23, "dfs"), (23, "audit")}
    seeds_path = ROOT / "n25-B16-cached-origin-seed-controls-20261005-v1/VERIFIED.json"
    seeds = read(seeds_path)
    assert seeds["verified"] and seeds["schema"] == "cached-support-actual-N25-fixed-seed-controls-v1"
    assert seeds["source_sha256"] == sha(ROOT / "test_cached_origin_seeds.py")
    assert seeds["seed_binary_sha256"] == sha(ROOT / "seed_cached_support_origin-linux")
    assert seeds["library_sha256"] == sha(library_path) and len(seeds["cases"]) == 4
    assert seeds["all_exact_attaining_seed_results_retained"]
    assert seeds["all_strict_source_seed_results_explicitly_paid"]
    for report in (maps, guard, seeds):
        unchanged(report["files_relative_to_workspace"])
        files.update(report["files_relative_to_workspace"])
    for path in (Path(__file__), library_path, maps_path, guard_path, seeds_path,
                 ROOT / "cached_support_gate.py", ROOT / "SPARSE-SUPPORT-NECESSARY-FILTERS.md",
                 ROOT / "SPARSE-SUPPORT-CACHE-SOURCE.md", ROOT / "cached-origin-seed-source-derivation.json",
                 ROOT / "sparse_support_cached_match-linux", ROOT / "peel_cached_support_origin_collar-linux",
                 driver_report_path, ROOT / "derive_cached_reboot_origin_driver.py",
                 ROOT / "run_reboot_origin_search.py", ROOT / "run_cached_reboot_origin_search.py"):
        bind(files, path)
    unchanged(files)
    return files
