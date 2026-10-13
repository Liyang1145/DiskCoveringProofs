"""N25 actual full sources, including their nonzero strict-library pruning.

Freshly replay the four actual strict libraries. Reuse original full source
exhaustion/union theorems under checked bytes, not a new enumeration or merge.
"""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction as F
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
WORK = ROOT.parents[2]
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from verify_sparse_maps_fast import library_gate
from group_catalog import validate
from batch_origin_collar import parent_gate
from test_sparse_collar import mechanical_derivation
from test_eight_rod_collar import derivation_gate as eight_derivation
from pending_degree_production_gate import production_gate as degree_gate
from cached_origin_production_gate import production_gate as cache_gate
from test_outer_collar import WSL, linux_path

assert __debug__
SOURCE_DOC = ROOT / "N25-ACTUAL-FOUR-SOURCE-OBLIGATIONS-v1.md"
STAGES = {
    14: ("n25-B14-sparse-collar-search-resume-20261005-v1", "peel_sparse_outer_collar-linux",
         "run_sparse_collar.py", "n25-B14-sparse-library-v1", 12, 172092),
    15: ("n25-B15-degree-origin-complete-search-20261005-v1", "peel_pending_degree_origin_collar-linux",
         "run_b15_degree_origin_replacement.py", "n25-B15-offline-contracted-union27-library-20261005-v1",
         27, 139315),
    16: ("n25-B16-cached-origin-streamed-search-reboot-20261005-v1", "peel_cached_support_origin_collar-linux",
         "run_cached_reboot_origin_search.py", "n25-B16-offline-union-sparse-library-20261005-v1",
         164, 120782),
    17: ("n25-B17-origin-streamed-search-reboot-20261005-v1", "peel_origin_streamed_collar-linux",
         "run_reboot_origin_search.py", "n25-B17-new-sparse-library-20261005-v1", 20, 289140),
}


def record_gate(receipt, B, total):
    assert receipt["N"] == 25 and receipt["B"] == B and receipt["necessary_weak_graphs"] == total
    assert receipt["actual_original_native_success_and_source_contents_checked"]
    assert receipt["full_root_no_fixed_seed_unlimited_DFS"]
    assert receipt["all_actual_loaded_strict_library_trees_fresh_exact_replayed"]
    assert receipt["positive_returns_always_validate_full_center_anchor_and_face_injection"]
    assert receipt["samples_not_claimed_all_pruned_states_independent_logs"]
    assert receipt["old_entire_catalog_union_and_mapping_theorems_reused_under_unchanged_bytes"]
    assert receipt["residual_graphs_not_complete_types_or_paid_lower_bounds"]
    assert receipt["node_limit"] == 0 and not receipt["global_optimality_proved"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    mechanical_derivation()
    eight_derivation()
    originpath = ROOT / "origin-streamed-collar-source-derivation.json"
    origin = read(originpath)
    assert origin["verified_mechanical_derivation"]
    assert origin["source_sha256"] == sha(ROOT / "derive_origin_streamed_collar.py")
    original, derived = ROOT / "peel_streamed_collar.cpp", ROOT / "peel_origin_streamed_collar.cpp"
    assert origin["original_source_sha256"] == sha(original) and origin["derived_source_sha256"] == sha(derived)
    text = original.read_text(encoding="utf8")
    for (before, after), count in zip(origin["changes"], origin["occurrence_counts"], strict=True):
        assert text.count(before) == count == 1
        text = text.replace(before, after)
    assert text == derived.read_text(encoding="utf8")
    budgetpath = ROOT / "n25-own-exact-family-budget-v1/VERIFIED.json"
    budget = read(budgetpath)
    assert budget["verified"] and budget["N"] == 25
    assert budget["source_sha256"] == sha(ROOT / "verify_n25_own_family_budget.py")
    assert budget["necessary_boundary_internal_families"] == [[b, 25-b] for b in range(14, 18)]
    assert budget["own_two_four_six_eight_rod_caps"] == [768677, 1587443, 2546859, 4058615]
    files, receipts = {}, []

    def add(path, digest=None):
        path = Path(path).resolve()
        assert path.is_file() and path.is_relative_to(WORK), ("source binding escapes actual workspace", path)
        if digest is None:
            digest = sha(path)
        assert sha(path) == digest, ("source premise content differs", path)
        key = str(path)
        assert key not in files or files[key] == digest
        files[key] = digest

    def relative_bindings(bindings):
        for name, digest in bindings.items():
            assert not Path(name).is_absolute()
            add(WORK / name, digest)

    for B, (directory, binary, driver, libraryname, patterns, total) in STAGES.items():
        stage, librarypath = ROOT / directory, ROOT / libraryname / "LIBRARY.json"
        print("N25 own actual source and strict-library fresh gate:", B, patterns, "patterns", flush=True)
        constants, library, table, libraryfiles = library_gate(librarypath)
        assert (library["source_N"], library["B"], library["obstacle_count"]) == (25, B, patterns)
        assert F(constants["radius_upper"]) == F(239146311738101, 10**15)
        assert constants["angle_scale"] == 10**7 and constants["angle_caps"] == [768677, 1587443, 2546859]
        relative_bindings(libraryfiles)
        add(librarypath)
        add(table, library["pattern_table_sha256"])
        inputs, summary, terminal = map(read, (
            stage / "INPUT-BINDINGS.json", stage / "SUMMARY.json", stage / "NATIVE-TERMINAL.json"))
        assert summary["verified"] and (summary["N"], summary["B"]) == (25, B)
        assert summary["complete_necessary_outer_collar_overapproximation"]
        assert summary["source_sha256"] == sha(ROOT / driver)
        assert summary["unpaid_weak_graphs"] == total
        assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] == 0
        assert terminal["native_log_sha256"] == sha(stage / "NATIVE-STDERR.log")
        relative_bindings(inputs["files_relative_to_workspace"])
        relative_bindings(summary["files_relative_to_workspace"])
        catalogname = ("N25-B14-necessary-sparse-collars.json" if B == 14
                       else f"N25-B{B}-complete-origin-sorted-chunks.json")
        manifestpath = stage / catalogname
        native = read(manifestpath)
        assert native["complete_necessary_outer_search"] and not native["complete_full_triangulations"]
        assert (native["N"], native["B"], native["mode"], native["screen"]) == (25, B, "dfs", True)
        assert native["scale"] == constants["angle_scale"] and native["caps"] == constants["angle_caps"]
        assert not native.get("seeded_fixed_collar_restriction", False)
        assert native["proof_prunes"] == native["paid_patterns_loaded"] == 0 and not native["proof_payments"]
        assert native["sparse_patterns_loaded"] == patterns
        assert native["sparse_proof_prunes"] == sum(item["pruned_recursive_states"] for item in native["sparse_payments"])
        expected = [
            WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
            "./"+binary, "25", str(B), manifestpath.relative_to(ROOT).as_posix(), "10000000",
            "768677", "1587443", "2546859", "0", "dfs", "-", table.relative_to(ROOT).as_posix()]
        if B != 14:
            expected += ["4058615", "100000", "1"]
        if B == 15:
            expected += ["1"]
        assert inputs["command"] == expected
        matcher = ROOT / ("sparse_outer_matcher.inc" if B in (14, 17) else "sparse_support_cached_matcher.inc")
        matchertext = matcher.read_text(encoding="utf8")
        paymentbody = matchertext.split("bool already_sparse_paid(State const& state) {", 1)[1].split(
            "void write_sparse_summary", 1)[0]
        assert paymentbody.index("if(match.id<0)return false;") < paymentbody.index(
            "verify_sparse_injection(raw,match);") < paymentbody.index("sparse_prunes++;")
        assert paymentbody.count("return true;") == 1
        byid = {item["id"]: item for item in library["obstacles"]}
        for item in native["sparse_payments"]:
            assert item["obstacle"] in byid and item["pruned_recursive_states"] > 0
            obstacle = byid[item["obstacle"]]
            mapping = {key: item[key] for key in ("centers", "anchors", "orientation", "shift")}
            validate(25, B, obstacle["faces"], mapping, item["sample_faces"])
        if B == 14:
            assert native["schema"] == "outer-collar-overapproximation-v1"
            assert native["weak_graph_count"] == len(native["weak_graphs"]) == total
            assert summary["native_catalog_sha256"] == sha(manifestpath)
            groupspath = stage / "GROUPS.json"
            groups = read(groupspath)
            assert summary["groups_sha256"] == sha(groupspath)
            assert groups["group_count"] == total and len(groups["groups"]) == total
            assert groups["full_selected_catalog_scanned"] and groups["verified_embeddings_during_generation"]
            add(groupspath)
            add(stage / groups["bindings_file"], groups["bindings_sha256"])
            sourceacceptance = ROOT / "n25-B14-all-parent-lower-chain-audit-20261005-v1/VERIFIED.json"
            paid = read(sourceacceptance)
            assert paid["verified"] and paid["source_sha256"] == sha(ROOT / "audit_n25_b14_chain.py")
            assert paid["complete_necessary_parent_weak_graphs"] == total and paid["pending_weak_graphs"] == 0
            assert paid["each_parent_id_has_exactly_one_final_status"]
            assert paid["files_relative_to_workspace"][manifestpath.relative_to(WORK).as_posix()] == sha(manifestpath)
            add(sourceacceptance)
        else:
            assert native["cap8"] == 4058615 and native["eight_rod_screen"] and native["origin_cover_screen"]
            assert native["origin_cover_only_N25"]
            assert native["origin_cover_scope"] == "actual arbitrary disk covers only; not weak graph geometry"
            assert F(native["origin_radius_upper_numerator"], native["origin_radius_upper_denominator"]) == F(constants["radius_upper"])
            assert summary["actual_arbitrary_cover_origin_condition_used"]
            unionpath = stage / "UNION/VERIFIED.json"
            union, catalogpath, bindingpath = parent_gate(manifestpath, stage / "NATIVE-TERMINAL.json", unionpath)
            assert union["unique_necessary_weak_graphs"] == total
            assert summary["native_manifest_sha256"] == sha(manifestpath)
            assert summary["complete_union_report_sha256"] == sha(unionpath)
            assert summary["catalog_sha256"] == sha(catalogpath)
            for path in (unionpath, catalogpath, bindingpath):
                add(path)
            for item, audited in zip(native["chunks"], union["input_chunks"], strict=True):
                add(ROOT / item["file"], audited["sha256"])
            sourceacceptance = unionpath
        if B == 15:
            assert native["pending_degree_upper_screen"]
            maps = ROOT / "n25-B15-union27-sparse-map-controls-20261005-v1/VERIFIED.json"
            guard = ROOT / "n25-B15-union27-eight-sparse-guard-controls-20261005-v1/VERIFIED.json"
            relative_bindings(degree_gate(librarypath, maps, guard, B))
        elif B == 16:
            maps = ROOT / "n25-B16-cached-support-map-controls-20261005-v1/VERIFIED.json"
            guard = ROOT / "n25-B16-cached-support-all-four-partition-controls-20261005-v1.json"
            relative_bindings(cache_gate(librarypath, maps, guard, B))
        elif B == 17:
            mapspath = ROOT / "n25-B17-eight-sparse-map-controls-20261005-v1/VERIFIED.json"
            guardpath = ROOT / "n25-B17-eight-sparse-guard-controls-20261005-v1/VERIFIED.json"
            maps, guard = read(mapspath), read(guardpath)
            assert maps["verified"] and guard["verified"]
            assert maps["library_sha256"] == guard["library_sha256"] == sha(librarypath)
            assert maps["all_source_trees_fresh_exact_replayed"]
            assert maps["source_sha256"] == sha(ROOT / "verify_sparse_maps_fast.py")
            assert maps["matcher_include_sha256"] == sha(matcher)
            assert guard["source_sha256"] == sha(ROOT / "test_eight_sparse_guard.py")
            assert guard["maps_controls_sha256"] == sha(mapspath)
            assert guard["all_baseline_minus_residual_graphs_individually_paid"]
            assert len(guard["cases"]) == 4
            assert all(item["all_removed_weak_graphs_explicitly_paid"] for item in guard["cases"])
            relative_bindings(maps["files_relative_to_workspace"])
            relative_bindings(guard["files_relative_to_workspace"])
            add(mapspath)
            add(guardpath)
        for path in (manifestpath, stage / "INPUT-BINDINGS.json", stage / "SUMMARY.json",
                     stage / "NATIVE-TERMINAL.json", stage / "NATIVE-STDERR.log",
                     stage / "WSL-LAUNCH.json", ROOT / driver, ROOT / binary, matcher):
            add(path)
        receipt = {
            "N": 25, "B": B, "necessary_weak_graphs": total, "node_limit": 0,
            "actual_original_native_success_and_source_contents_checked": True,
            "full_root_no_fixed_seed_unlimited_DFS": True,
            "all_actual_loaded_strict_library_trees_fresh_exact_replayed": True,
            "positive_returns_always_validate_full_center_anchor_and_face_injection": True,
            "samples_not_claimed_all_pruned_states_independent_logs": True,
            "old_entire_catalog_union_and_mapping_theorems_reused_under_unchanged_bytes": True,
            "residual_graphs_not_complete_types_or_paid_lower_bounds": True,
            "sparse_library_patterns": patterns, "sparse_proof_prunes_not_types": native["sparse_proof_prunes"],
            "library_sha256": sha(librarypath), "native_manifest_sha256": sha(manifestpath),
            "original_source_summary_sha256": sha(stage / "SUMMARY.json"),
            "complete_source_acceptance_sha256": sha(sourceacceptance),
            "actual_native_binary": binary, "actual_native_binary_sha256": sha(ROOT / binary),
            "origin_paid_in_source": B != 14, "pending_degree_upper_in_source": B == 15,
            "support_candidate_cache_in_source": B in (15, 16),
            "full_DFS_state_omission_cache_in_selected_source": False,
            "global_optimality_proved": False}
        record_gate(receipt, B, total)
        receipts.append(receipt)
        print("N25 complete original source, all actual strict patterns, and injection gate passed:", B,
              total, "residual necessary weak graphs", flush=True)
    refused = []
    for field, value in (
        ("N", 24), ("B", 15), ("necessary_weak_graphs", 172091), ("node_limit", 1),
        ("actual_original_native_success_and_source_contents_checked", False),
        ("full_root_no_fixed_seed_unlimited_DFS", False),
        ("all_actual_loaded_strict_library_trees_fresh_exact_replayed", False),
        ("positive_returns_always_validate_full_center_anchor_and_face_injection", False),
        ("samples_not_claimed_all_pruned_states_independent_logs", False),
        ("old_entire_catalog_union_and_mapping_theorems_reused_under_unchanged_bytes", False),
        ("residual_graphs_not_complete_types_or_paid_lower_bounds", False),
        ("global_optimality_proved", True)):
        wrong = deepcopy(receipts[0])
        wrong[field] = value
        try:
            record_gate(wrong, 14, 172092)
        except (AssertionError, KeyError):
            refused.append(field)
        else:
            raise AssertionError("incorrect full N25 source scope accepted: "+field)
    for path in (
        Path(__file__), SOURCE_DOC, budgetpath, originpath,
        ROOT / "NECESSARY-OUTER-COLLAR-ARBITRARY-COVER-INDUCTION-v1.md",
        ROOT / "N23-N24-COVER-AND-FULL-PEEL-INDUCTION-v1.md",
        ROOT / "PENDING-DEGREE-UPPER-SOURCE.md", ROOT / "SPARSE-SUPPORT-CACHE-SOURCE.md",
        ROOT / "SPARSE-SUPPORT-NECESSARY-FILTERS.md", ROOT / "SPARSE-OUTER-OBSTACLE-TRANSPORT.md",
        ROOT / "pending_degree_upper.inc", ROOT / "peel_pending_degree_origin_collar.cpp",
        ROOT / "peel_cached_support_origin_collar.cpp", ROOT / "peel_origin_streamed_collar.cpp",
        ROOT / "batch_origin_collar.py", ROOT / "verify_sparse_maps_fast.py",
        ROOT / "family_sparse_gate.py", HIGH / "group_catalog.py", HIGH / "exact_graph.py"):
        add(path)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N25-four-actual-complete-necessary-sources-and-all-nonzero-strict-library-guards-v1",
        "N": 25, "necessary_boundary_internal_families": [[b, 25-b] for b in range(14, 18)],
        "complete_necessary_residual_weak_graph_counts": [172092, 139315, 120782, 289140],
        "total_necessary_residual_weak_graphs": 721329, "source_receipts": receipts,
        "actual_223_loaded_strict_library_trees_fresh_exactly_mathematically_reaccepted": True,
        "all_selected_actual_nonzero_pruning_uses_fully_validated_injection_on_each_positive_return": True,
        "correct_B14_origin_later_payment_and_B15_degree_upper_and_B15_B16_candidate_cache_scopes": True,
        "old_full_enumerations_and_exact_unions_honestly_reused_not_claimed_new_large_runs": True,
        "written_cover_full_peeling_omission_and_positive_guard_transport_reviewed_math_premises": True,
        "written_math_not_claimed_machine_proved_by_hash_or_small_cases": True,
        "source_document_sha256": sha(SOURCE_DOC), "family_budget_sha256": sha(budgetpath),
        "negative_full_source_scope_controls_rejected": refused, "frozen_files": files,
        "source_sha256": sha(Path(__file__)),
        "all_parent_lower_chains_same_root_upper_core_and_global_freeze_still_required": True,
        "global_optimality_proved": False})
    print("N25 four actual complete necessary sources and all nonzero strict library guards accepted;",
          "final lower/global assembly still owed", flush=True)


if __name__ == "__main__":
    main()
