"""Full content closure for all four actual N24 sources and accepted lower chains."""
from pathlib import Path
from collections import deque
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
WORK = ROOT.parents[2]
INCOMING = ROOT.parents[4]
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from n24_actual_core_transport import own_core_gate, COREPATH, SYSTEMPATH

assert __debug__
SOURCEPATH = ROOT / "n24-four-complete-source-interfaces-v1/VERIFIED.json"
EXPECTED = {
    13: (4202, 4049, 153, 0, 0),
    14: (10812, 4919, 5892, 1, 0),
    15: (31348, 23296, 7959, 92, 1),
    16: (82816, 66067, 16576, 173, 0),
}


def final_gate(B, source, lower, base, final):
    total, weak, filling, refined, core = EXPECTED[B]
    assert all(item["verified"] for item in (source, lower, base, final))
    assert source["schema"] == "small-order-complete-necessary-origin-outer-family-source-and-union-v1"
    assert (source["N"], source["B"], source["unique_necessary_weak_graphs"]) == (24, B, total)
    assert lower["source_sha256"] == sha(ROOT / "small_order_collar_lower_pipeline.py")
    assert (lower["N"], lower["B"], lower["parent_weak_graphs"], lower["strictly_excluded"]) == (24, B, total, weak)
    assert base["source_sha256"] == sha(ROOT / "small_order_parent_fillings.py")
    assert base["parent_weak_graphs"] == total and base["old_strict_weak_graphs"] == weak
    assert base["new_strict_complete_families"] == filling
    assert base["pending_families"] == refined+core
    assert base["full_parent_partition_complete"]
    if B == 13:
        assert final == base and final["pending_families"] == 0
        assert final["complete_source_lower_family_paid"]
    elif B == 15:
        assert final["schema"] == "N24-full-parent-own-strict-and-same-root-core-supplement-disjoint-adoption-v1"
        assert final["source_sha256"] == sha(ROOT / "audit_n24_mixed_parent_supplements.py")
        assert final["new_strict_refined_complete_families"] == refined
        assert final["new_own_strict_and_same_root_core_complete_families"] == core
        assert final["remaining_pending_families"] == 0 and final["whole_parent_family_lower_paid"]
        assert final["full_parent_disjoint_partition_complete"]
        assert final["core_remains_nonstrict_same_root_not_strict_upper_exclusion"]
        assert final["all_core_leaf_center_anchor_face_and_witness_rods_bound_to_own_N24_theorem"]
    else:
        assert final["schema"] == "small-order-formal-complete-parent-strict-refinement-disjoint-adoption-v1"
        assert final["source_sha256"] == sha(ROOT / "audit_small_order_parent_supplements.py")
        assert final["new_strict_complete_refined_families"] == refined
        assert final["remaining_pending_families"] == 0 and final["whole_parent_family_lower_paid"]
        assert final["controls_sha256"] == sha(ROOT / "small-order-parent-supplement-controls-v2/VERIFIED.json")
    assert (final["N"], final["B"]) == (24, B)
    if B != 13:
        assert final["complete_parent_weak_graphs"] == total
        assert final["old_strict_weak_graphs"] == weak
        assert final["old_strict_complete_families"] == filling
    assert weak+filling+refined+core == total


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    sourceinterface = read(SOURCEPATH)
    assert sourceinterface["verified"] and sourceinterface["source_sha256"] == sha(ROOT / "verify_n24_complete_source_interfaces.py")
    assert sourceinterface["necessary_boundary_internal_families"] == [[13, 11], [14, 10], [15, 9], [16, 8]]
    assert sourceinterface["complete_necessary_weak_graph_counts"] == [4202, 10812, 31348, 82816]
    assert sourceinterface["total_necessary_weak_graphs"] == 129178
    coreproof = own_core_gate()
    budgetpath = ROOT / "n23-n24-own-family-budget-v1/VERIFIED.json"
    budget = read(budgetpath)
    ownbudget = next(item for item in budget["orders"] if item["N"] == 24)
    assert ownbudget["fresh_root_report_sha256"] == coreproof["fresh_root_report_sha256"]
    pending, bindings, reasons, inspected = deque(), {}, {}, set()
    allowed = (INCOMING, INCOMING.parent / "dependencies")
    def add(path, expected=None, reason="immutable-original-mathematical-premise"):
        path = Path(path).resolve()
        assert any(path.is_relative_to(root) for root in allowed), ("binding escapes reviewed proof roots", path)
        assert path.is_file(), ("missing required full proof evidence", path)
        if expected is None:
            expected = sha(path)
        assert type(expected) is str and len(expected) == 64
        if path in bindings:
            assert expected == bindings[path], ("conflicting content identities", path)
            return
        bindings[path], reasons[path] = expected, reason
        if path.suffix == ".json" and (
            path.name in ("VERIFIED.json", "SOURCE-ACCEPTED.json", "EXACT.json", "SUMMARY.json",
                          "INPUT-BINDINGS.json", "EXACT-REPLAY.json",
                          "FRESH-LOCAL-ISOLATION.json", "FRESH-ANGLE-REPLAY.json")
            or path.name.endswith("-EXACT.json") or path.name.endswith("-verified.json")):
            pending.append(path)
    for path in (
        Path(__file__), SOURCEPATH, budgetpath, COREPATH, SYSTEMPATH,
        ROOT / "N24-GLOBAL-SOURCE-PROOF-v1.md",
        ROOT / "N23-N24-COVER-AND-FULL-PEEL-INDUCTION-v1.md",
        ROOT / "NECESSARY-OUTER-COLLAR-ARBITRARY-COVER-INDUCTION-v1.md",
        ROOT / "SMALL-ORDER-COMPLETE-FILLING-SOURCE-v1.md",
        ROOT / "small-order-parent-supplement-controls-v2/VERIFIED.json",
        ROOT / "n24-mixed-parent-supplement-controls-v1/VERIFIED.json",
        ROOT / "n24-own-core-transport-controls-v1/VERIFIED.json",
        ROOT / "n24-mixed-core-controls-v2/VERIFIED.json"):
        add(path)
    families = []
    for B in range(13, 17):
        sourcepath = ROOT / f"n24-B{B}-s1/ACCEPTED/SOURCE-ACCEPTED.json"
        lowerdir, basedir = ROOT / f"n24-B{B}-l1", ROOT / f"n24-B{B}-f1"
        finaldir = basedir / "ACCEPTED" if B == 13 else ROOT / f"n24-B{B}-final1"
        lowerpath, basepath, finalpath = lowerdir / "ACCEPTED/VERIFIED.json", basedir / "ACCEPTED/VERIFIED.json", finaldir / "VERIFIED.json"
        source, lower, base, final = map(read, (sourcepath, lowerpath, basepath, finalpath))
        final_gate(B, source, lower, base, final)
        assert lower["source_acceptance_sha256"] == base["source_acceptance_sha256"] == sha(sourcepath)
        assert base["old_weak_lower_report_sha256"] == sha(lowerpath)
        if B != 13:
            assert final["source_acceptance_sha256"] == sha(sourcepath)
            assert final["base_report_sha256"] == sha(basepath)
        families.append({
            "B": B, "total": EXPECTED[B][0], "strict_weak": EXPECTED[B][1],
            "strict_complete_first": EXPECTED[B][2], "strict_complete_final": EXPECTED[B][3],
            "own_nonstrict_mixed_complete": EXPECTED[B][4], "pending": 0,
            "source_sha256": sha(sourcepath), "lower_sha256": sha(lowerpath),
            "base_sha256": sha(basepath), "final_sha256": sha(finalpath), "final_path": str(finalpath)})
        for path in (sourcepath, lowerpath, basepath, finalpath,
                     lowerdir / "INPUT-BINDINGS.json", lowerdir / "PARTITION.json",
                     lowerdir / "PIPELINE-COMPLETED.json", lowerdir / "AUDIT-TERMINAL.json",
                     basedir / "INPUT-BINDINGS.json", basedir / "PARTITION.json",
                     basedir / "PIPELINE-COMPLETED.json", basedir / "AUDIT-TERMINAL.json"):
            add(path)
        for directory in (lowerdir, basedir):
            pipeline = read(directory / "PIPELINE-COMPLETED.json")
            terminal = read(directory / "AUDIT-TERMINAL.json")
            assert pipeline["report_sha256"] == sha(directory / "ACCEPTED/VERIFIED.json")
            assert terminal["actual_exit_code"] == 0 and terminal["actual_child_terminal_observed"]
        for ledgerdir, report, fields in (
            (lowerdir / "ACCEPTED", lower,
             (("PAYMENTS.jsonl", "payments_sha256"), ("PENDING.jsonl", "pending_sha256"),
              ("AUDITED-STAGES.jsonl", "audited_stages_sha256"))),
            (basedir / "ACCEPTED", base,
             (("ADDITIONAL-PAYMENTS.jsonl", "additional_payments_sha256"),
              ("PENDING.jsonl", "pending_sha256"), ("AUDITED-JOBS.jsonl", "audited_jobs_sha256"))),
            (finaldir, final,
             (("ADDITIONAL-PAYMENTS.jsonl", "additional_payments_sha256"), ("PENDING.jsonl", "pending_sha256")))):
            for name, field in fields:
                add(ledgerdir / name, report[field])
        assert (finaldir / "PENDING.jsonl").stat().st_size == 0
        with (lowerdir / "ACCEPTED/AUDITED-STAGES.jsonl").open(encoding="ascii") as stream:
            index, paid = 0, 0
            for line in stream:
                item = json.loads(line, object_pairs_hook=no_duplicate_keys)
                assert item["batch"] == index
                directory = lowerdir / f"batch-{index:06}"
                for path, field in (
                    (directory / "GROUPS.json", "groups_sha256"),
                    (directory / "bindings.jsonl", "bindings_sha256"),
                    (directory / "PROPOSALS/SUMMARY.json", "receipt_sha256"),
                    (directory / "PROPOSALS/EXACT-REPLAY.json", "exact_replay_sha256"),
                    (directory / "TERMINAL.json", "proof_terminal_sha256"),
                    (directory / "PROPOSALS/REPLAY-TERMINAL.json", "replay_terminal_sha256")):
                    add(path, item[field])
                receipt = read(directory / "PROPOSALS/SUMMARY.json")
                for outcome in receipt["outcomes"]:
                    if outcome["status"] == "excluded":
                        add(directory / f"PROPOSALS/group-{outcome['group']:07}.json.gz", outcome["tree_sha256"])
                        paid += 1
                index += 1
            assert paid == lower["strictly_excluded"]
        add(basedir / "JOBS.jsonl")
        add(basedir / "COMPLETED-JOBS.jsonl")
        with (basedir / "ACCEPTED/AUDITED-JOBS.jsonl").open(encoding="ascii") as stream:
            for line in stream:
                item = json.loads(line, object_pairs_hook=no_duplicate_keys)
                directory = basedir / f"batch-{item['job']:06}"
                add(directory / "SUMMARY.json", item["worker_report_sha256"])
                add(directory / "TERMINAL.json", item["terminal_sha256"])
                add(basedir / f"job-{item['job']:06}.json", item["job_sha256"])
        if B != 13:
            manifestname = ("n24-B15-all-mixed-supplements1.json" if B == 15
                            else f"n24-B{B}-all-supplements1.json" if B == 16
                            else "n24-B14-final-supplements1.json")
            manifestpath = ROOT / manifestname
            manifest = read(manifestpath)
            assert final["supplements_manifest_sha256"] == sha(manifestpath) if B != 15 else (
                final["frozen_files"][str(manifestpath)] == sha(manifestpath))
            add(manifestpath)
            assert manifest["base_report_sha256"] == sha(basepath)
            for path, digest in manifest["supplement_origin_records_sha256"].items():
                add(path, digest)
            for item in manifest["additions"]:
                for key, field in (("proof_path", "proof_sha256"), ("exact_path", "exact_sha256")):
                    add(item[key], item[field])
    while pending:
        path = pending.popleft()
        if path in inspected:
            continue
        inspected.add(path)
        record = read(path)
        for field in ("frozen_files", "files_relative_to_workspace"):
            for name, digest in record.get(field, {}).items():
                target = Path(name) if field == "frozen_files" else WORK / name
                assert target.is_absolute()
                add(target, digest)
        for name, archive in record.get("archive_bindings", {}).items():
            if not isinstance(archive, dict) or "archive_sha256" not in archive:
                continue
            target = Path(name)
            if not target.is_absolute():
                assert target.name == name
                target = INCOMING / name
            add(target, archive["archive_sha256"], "original-verified-whole-archive-premise")
    output.mkdir()
    print("N24 entire four-family source/lower/root byte closure collected:", len(bindings),
          "actual current files or whole archives; all accepted exact math reused honestly", flush=True)
    mismatches = []
    with (output / "CURRENT-INPUTS.jsonl").open("x", encoding="ascii") as ledger:
        for number, path in enumerate(sorted(bindings, key=str), 1):
            if sha(path) != bindings[path]:
                mismatches.append(str(path))
            ledger.write(json.dumps({
                "path": str(path), "sha256": bindings[path], "origin": reasons[path]},
                separators=(",", ":"))+"\n")
            if number % 5000 == 0:
                print("N24 complete current source-proof prerequisite bytes", number,
                      "/", len(bindings), "differences", len(mismatches), flush=True)
    assert not mismatches, mismatches
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N24-four-whole-necessary-family-same-root-global-premise-current-byte-closure-v1",
        "N": 24, "all_required_families": [13, 14, 15, 16],
        "all_complete_sources_and_final_parent_lower_chains_zero": True,
        "total_necessary_weak_graphs": 129178, "family_partitions": families,
        "all_real_own_core_full_leaves_rod_transport_and_nonstrict_status_bound": True,
        "all_current_evidence_files_and_whole_archives": len(bindings),
        "all_current_content_bindings_checked": True, "mismatches": mismatches,
        "recursively_inspected_bound_evidence_reports": len(inspected),
        "current_input_ledger_sha256": sha(output / "CURRENT-INPUTS.jsonl"),
        "same_root_proof_sha256": sha(COREPATH), "system_sha256": sha(SYSTEMPATH),
        "source_interface_sha256": sha(SOURCEPATH), "family_budget_sha256": sha(budgetpath),
        "global_source_manuscript_sha256": sha(ROOT / "N24-GLOBAL-SOURCE-PROOF-v1.md"),
        "old_mathematics_honestly_reused_not_new_complete_old_tree_replays": True,
        "written_math_not_claimed_machine_proved_by_hash_checks": True,
        "source_sha256": sha(Path(__file__)),
        "independent_full_current_byte_audit_and_final_global_adoption_still_required": True,
        "global_optimality_proved": False})
    print("N24 complete four-family global mathematical premises current content closure accepted;",
          "final independent global audit still required", flush=True)


if __name__ == "__main__":
    main()
