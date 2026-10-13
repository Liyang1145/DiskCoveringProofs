"""Check the entire immutable original B15 incremental lower-payment chain.

Accepted mathematical source-row scans and tree replays remain unchanged
premises; this does not pretend to do a new whole-16M mathematical scan.
"""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from audit_streamed_hierarchy import check_map

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    basepath = ROOT / "n23-B15-origin-and-original-pair-disjoint-merge-20261005-v1/VERIFIED.json"
    base = read(basepath)
    assert base["verified"] and (base["N"], base["B"], base["catalog_types"]) == (23, 15, 16790546)
    assert base["all_16790546_source_indices_partitioned_once"]
    assert base["all_5690_positive_pair_force_trees_fresh_replayed_again"]
    assert base["old_strict_and_origin_overlap_deducted_not_double_counted"]
    assert base["payment_counts"] == {
        "actual-cover-origin-obstruction": 13014588, "pending": 2852476,
        "overlap_not_counted_twice": 2263815, "additional-strict-pair-force": 923482}
    assert 13014588+923482+2852476 == 16790546
    stages = [
        ("n23-B15-effective-outer-all-source-payment-audit-20261005-v1", 2852476, 793841, 2058635),
        ("n23-B15-residual-new6772-outer-full-source-audit-20261005-v1", 793841, 33861, 759980),
        ("n23-B15-residual-new61-force127-full-source-audit-20261006-v1", 33861, 14536, 19325),
        ("n23-B15-residual-new32-force511-full-source-audit-solo-v1", 14536, 3976, 10560),
        ("n23-B15-residual-new4-force1001-full-source-audit-solo-v1", 3976, 2978, 998),
        ("n23-B15-residual-new7-force5001-full-source-audit-solo-v1", 2978, 829, 2149),
    ]
    chain, previous, paths = [], basepath, [basepath]
    for index, (directory, before, after, extra) in enumerate(stages):
        path = ROOT / directory / "VERIFIED.json"
        record = read(path)
        assert record["verified"] and (record["N"], record["B"], record["original_catalog_types"]) == (23, 15, 16790546)
        assert record["parent_payment_report_sha256"] == sha(previous)
        assert record["previous_pending_full_types"] == before and record["pending_full_types"] == after
        assert record["additional_strict_outer_types"] == extra and before == extra+after
        assert record["old_paid_source_types_not_recounted"] if index == 0 else (
            record["only_previous_pending_source_types_paid_no_prior_payment_recount"])
        if index == 0:
            assert record["all_original_source_rows_and_complete_end_of_file_checked"]
            assert record["all_previous_unpaid_source_face_center_anchor_maps_independently_checked"]
            assert record["all_22857_positive_outer_trees_freshly_exact_replayed_again"]
        else:
            assert record["all_source_indices_and_original_outer_bindings_scanned"]
            assert record["every_previous_unpaid_actual_face_center_anchor_map_freshly_checked"]
            assert record["all_new_positive_trees_independently_freshly_exact_replayed_again"]
            assert record["known_attaining_outer_group_explicitly_retained"] == 522460
        pendingpath, extrapath = path.parent / "PENDING.jsonl", path.parent / "ADDITIONAL-PAYMENTS.jsonl"
        assert sha(pendingpath) == record["pending_sha256"]
        assert sha(extrapath) == record["additional_payments_sha256"]
        chain.append({"previous": before, "strict_extra": extra, "pending": after,
                      "report": str(path), "sha256": sha(path)})
        paths.extend((path, pendingpath, extrapath))
        previous = path
    restorationpath = ROOT / "n23-B15-actual829-full-residual-types-solo-v1/VERIFIED.json"
    restoration = read(restorationpath)
    assert restoration["verified"] and restoration["parent_report_sha256"] == sha(previous)
    assert restoration["actual_full_residual_types"] == 829
    assert restoration["only_current_parent_pending_indices_selected"]
    assert restoration["all_original_source_rows_and_bindings_scanned_to_real_end"]
    currentpath = ROOT / "n23-B15-actual829-force31-and-nonstrict-core-pipeline-solo-v1/ACTUAL-TYPE-PAYMENT-AUDIT/VERIFIED.json"
    current = read(currentpath)
    assert current["verified"] and current["parent_residual_restoration_report_sha256"] == sha(restorationpath)
    assert current["previous_pending_full_types"] == 829 and current["pending_full_types"] == 13
    assert current["counts"] == {
        "strict-complete-type-force": 815, "pending": 13, "nonstrict-same-root-core": 1}
    for flag in (
        "every_actual_current_residual_source_index_partitioned_once",
        "all_29_faces_in_every_strict_full_type_tree_independently_bound_and_replayed",
        "nonstrict_core_requires_complete_actual_type_map_and_fresh_core_prerequisites",
        "outer_group_identity_alone_never_pays_all_group_members"):
        assert current[flag]
    corepath = ROOT / "n23-nonstrict-core-fresh-root-upper-local-angle-audit-solo-v1/VERIFIED.json"
    core = read(corepath)
    systempath = ROOT / "n23-n24-archive-core-inputs-20261005-v1/n23/core-system.json"
    system = read(systempath)
    candidate = sorted(sum(1 << v for v in face) for face in system["all_faces"])
    assert len(candidate) == 29 and core["system_sha256"] == sha(systempath)
    corepayments = []
    paymentspath = currentpath.parent / "PAYMENTS.jsonl"
    assert sha(paymentspath) == current["payments_sha256"]
    with paymentspath.open(encoding="ascii") as stream:
        for line in stream:
            item = json.loads(line, object_pairs_hook=no_duplicate_keys)
            if item["kind"] == "nonstrict-same-root-core":
                corepayments.append(item)
    assert len(corepayments) == 1 and corepayments[0]["core_proof_sha256"] == sha(corepath)
    fullpath = restorationpath.parent / restoration["full_types_file"]
    assert sha(fullpath) == restoration["full_types_sha256"]
    actual = None
    with fullpath.open(encoding="ascii") as stream:
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            if row["index"] == corepayments[0]["index"]:
                assert actual is None
                actual = row
    assert actual is not None
    check_map(23, 15, {"centers": 23, "faces": candidate},
              corepayments[0]["candidate_full_to_actual_map"], set(actual["faces"]), 0)
    assert len(actual["faces"]) == 29
    active = sorted(sum(1 << v for v in face) for face in system["active_faces"])
    assert active == core["core_faces"] and set(active) <= set(candidate)
    assert system["center_core_nodes"] == list(range(15, 38))
    assert system["edges"][:30] == (
        [[i, 15+i] for i in range(15)]+[[i, 15+(i+1) % 15] for i in range(15)])
    for index, face in enumerate(system["active_faces"]):
        assert system["edges"][30+3*index:33+3*index] == [[38+index, 15+v] for v in face]
    finalpath = ROOT / "n23-B15-final13-actual-full-types-strict-supplement-audit-solo-v1/VERIFIED.json"
    final = read(finalpath)
    assert final["verified"] and final["parent_report_sha256"] == sha(currentpath)
    assert final["previous_pending_full_types"] == final["additional_strict_complete_types"] == 13
    assert final["pending_full_types"] == 0 and final["original_catalog_types"] == 16790546
    assert final["counts"] == {"strict-complete-type-force": 828, "nonstrict-same-root-core": 1}
    assert final["every_actual_current_residual_source_index_partitioned_once"]
    assert final["previous_attaining_core_payment_preserved_nonstrict_not_recast_as_strict"]
    assert (finalpath.parent / "PENDING.jsonl").stat().st_size == 0
    assert sha(finalpath.parent / "PENDING.jsonl") == final["pending_sha256"]
    paidtotal = 13014588+923482+sum(row[3] for row in stages)+828+1
    assert paidtotal == 16790546
    paths.extend((restorationpath, currentpath, finalpath, corepath, systempath, fullpath, paymentspath))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-B15-entire-original-formal-incremental-chain-and-actual-core-identity-v1",
        "N": 23, "B": 15, "original_catalog_types": 16790546, "pending_types": 0,
        "origin_types": 13014588, "disjoint_additional_pair_types": 923482,
        "outer_incremental_payments": chain, "actual_full_strict_types": 828,
        "actual_full_same_root_nonstrict_types": 1, "actual_same_root_core_source_index": actual["index"],
        "every_parent_hash_pending_count_and_disjoint_increment_checked": True,
        "complete_candidate_actual_source_map_and_active_root_graph_freshly_rechecked": True,
        "old_full_scans_and_tree_mathematics_reused_not_falsely_claimed_new_replay": True,
        "frozen_files": {str(path): sha(path) for path in paths+[Path(__file__)]},
        "source_sha256": sha(Path(__file__)),
        "source_cover_other_families_and_global_freeze_still_required": True,
        "global_optimality_proved": False})
    print("N23 B15 whole formal chain and actual full-core transport identity accepted;",
          "original16790546 paid once, pending0; global freeze still required", flush=True)


if __name__ == "__main__":
    main()
