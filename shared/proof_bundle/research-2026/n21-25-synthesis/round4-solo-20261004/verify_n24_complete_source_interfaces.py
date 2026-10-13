"""Four own-order complete necessary sources bound to reviewed cover/collar induction."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from small_order_collar_lower_pipeline import source_gate
from small_order_origin_caps import parameters
from test_small_order_origin_collar import derivation

assert __debug__


def record_gate(source, B, total):
    assert source["verified"]
    assert source["schema"] == "small-order-complete-necessary-origin-outer-family-source-and-union-v1"
    assert (source["N"], source["B"], source["unique_necessary_weak_graphs"]) == (24, B, total)
    for flag in (
        "complete_recorded_necessary_outer_family",
        "actual_native_successful_terminal_and_exact_source_inputs_rechecked",
        "all_declared_sorted_slabs_and_full_union_independently_verified",
        "weak_graph_rows_not_full_type_lower_bound_payments"):
        assert source[flag]
    assert source["source_sha256"] == sha(ROOT / "audit_small_order_origin_union.py")
    assert not source["global_optimality_proved"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    changes = derivation()
    constants, cap8, caps = parameters(24)
    assert F(constants["radius_upper"]) == F(61325412542131, 250000000000000)
    assert cap8 == 4381913
    assert constants["families"] == [[13, 11], [14, 10], [15, 9], [16, 8]]
    budgetpath = ROOT / "n23-n24-own-family-budget-v1/VERIFIED.json"
    budget = read(budgetpath)
    assert budget["verified"] and budget["source_sha256"] == sha(ROOT / "verify_n23_n24_family_budget.py")
    own = next(item for item in budget["orders"] if item["N"] == 24)
    assert own["necessary_boundary_internal_families"] == constants["families"]
    corepath = ROOT / "n24-core-fresh-v1/VERIFIED.json"
    core = read(corepath)
    assert core["verified"] and core["fresh_root_report_sha256"] == own["fresh_root_report_sha256"]
    counts, receipts, files = [4202, 10812, 31348, 82816], [], {}
    for B, total in zip(range(13, 17), counts, strict=True):
        stage = ROOT / f"n24-B{B}-s1"
        source = source_gate(stage)
        record_gate(source, B, total)
        manifest = read(stage / "MANIFEST.json")
        assert manifest["proof_prunes"] == manifest["sparse_proof_prunes"] == 0
        assert not manifest["proof_payments"] and not manifest["sparse_payments"]
        assert manifest["mode"] == "dfs" and manifest["origin_cover_screen"]
        assert manifest["caps"] == constants["angle_caps"] and manifest["cap8"] == cap8
        assert manifest["origin_cover_orders"] == [23, 24]
        assert F(manifest["origin_radius_upper_numerator"], manifest["origin_radius_upper_denominator"]) == F(constants["radius_upper"])
        assert not manifest.get("seeded_fixed_collar_restriction", False)
        native = read(stage / "NATIVE-TERMINAL.json")
        union = read(stage / "UNION-TERMINAL.json")
        assert native["actual_exit_code"] == union["actual_exit_code"] == 0
        assert native["native_terminal_observed"] and union["independent_process_terminal_observed"]
        receipts.append({
            "N": 24, "B": B, "necessary_weak_graphs": total,
            "source_report_sha256": sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json"),
            "catalog_sha256": source["catalog_sha256"],
            "real_full_root_unlimited_DFS_no_seed_no_force_or_sparse_payments": True,
            "own_actual_cover_origin_condition_not_standalone_weak_geometry": True})
        for path, digest in source["frozen_files"].items():
            assert path not in files or files[path] == digest
            files[path] = digest
        for path in (stage / "ACCEPTED/SOURCE-ACCEPTED.json",
                     stage / "PIPELINE-COMPLETED.json", stage / "UNION-TERMINAL.json"):
            files[str(path)] = sha(path)
    negatives = []
    first = source_gate(ROOT / "n24-B13-s1")
    for field, value in (
        ("N", 25), ("B", 14), ("unique_necessary_weak_graphs", 4201),
        ("complete_recorded_necessary_outer_family", False),
        ("actual_native_successful_terminal_and_exact_source_inputs_rechecked", False),
        ("all_declared_sorted_slabs_and_full_union_independently_verified", False),
        ("weak_graph_rows_not_full_type_lower_bound_payments", False),
        ("source_sha256", "0"*64), ("global_optimality_proved", True)):
        bad = deepcopy(first)
        bad[field] = value
        try:
            record_gate(bad, 13, 4202)
        except (AssertionError, KeyError):
            negatives.append(field)
        else:
            raise AssertionError("bad complete own-order source scope accepted: "+field)
    for path in (
        Path(__file__), budgetpath, corepath,
        ROOT / "N23-N24-COVER-AND-FULL-PEEL-INDUCTION-v1.md",
        ROOT / "NECESSARY-OUTER-COLLAR-ARBITRARY-COVER-INDUCTION-v1.md",
        ROOT / "SMALL-ORDER-COMPLETE-FILLING-SOURCE-v1.md",
        ROOT / "small-order-filling-controls-v2/VERIFIED.json",
        ROOT / "test_small_order_origin_collar.py", ROOT / "small_order_origin_caps.py"):
        files[str(path)] = sha(path)
    for path, digest in files.items():
        assert sha(path) == digest
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N24-reviewed-arbitrary-cover-collar-induction-bound-to-four-actual-full-sources-v1",
        "N": 24, "necessary_boundary_internal_families": constants["families"],
        "complete_necessary_weak_graph_counts": counts,
        "total_necessary_weak_graphs": sum(counts), "source_receipts": receipts,
        "native_recursive_degree_and_canonical_body_literal_source_derivation": changes,
        "own_radius_and_two_four_six_eight_rod_caps_verified": caps,
        "written_cover_full_peeling_and_pure_internal_omission_induction_reviewed_as_math_premises": True,
        "no_written_math_falsely_machine_proved_by_hash_or_small_reference_cases": True,
        "own_same_root_budget_upper_core_and_four_sources_bound": True,
        "source_flags_or_counts_alone_not_claimed_complete": True,
        "negative_own_source_scope_controls_rejected": negatives, "frozen_files": files,
        "source_sha256": sha(Path(__file__)),
        "all_lower_chains_and_actual_core_family_adoption_global_freeze_still_required": True,
        "global_optimality_proved": False})
    print("N24 all four actual complete necessary sources bound to reviewed arbitrary-cover induction:",
          sum(counts), "weak graphs; final lower chains/global freeze still owed", flush=True)


if __name__ == "__main__":
    main()
