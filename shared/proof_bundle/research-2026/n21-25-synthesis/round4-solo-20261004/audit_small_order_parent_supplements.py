"""Adopt exact complete-family refinements only from a real finished full parent."""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish
from stream_catalog import sha, no_duplicate_keys
from small_order_parent_fillings import parent_gate
from small_order_collar_lower_pipeline import rows
from refine_small_order_family import audit as replay_refinement

assert __debug__


def source_identity(expected, collar, N, B):
    assert (collar["N"], collar["B"]) == (N, B)
    assert type(collar["actual_source_parent_index"]) is int
    assert collar["actual_source_parent_index"] == expected["parent_index"]
    assert collar["centers"] == expected["centers"] and collar["faces"] == expected["faces"]
    assert expected["status"] == "pending-complete-family"
    assert expected["not_an_exclusion"]


def supplement(item, expected, N, B):
    family, proofpath, exactpath = (Path(item[key]).resolve() for key in ("family", "proof_path", "exact_path"))
    assert all(path.is_relative_to(ROOT) for path in (family, proofpath, exactpath))
    assert item["parent_index"] == expected["parent_index"]
    collar = read(family / "INPUT-COLLAR.json")
    source_identity(expected, collar, N, B)
    exact = read(exactpath)
    assert exact["verified"] and exact["schema"] == "small-order-same-topology-leaf-refinement-independent-replay-v1"
    assert exact["source_sha256"] == sha(ROOT / "refine_small_order_family.py")
    assert exact["whole_completion_family_strictly_closed"]
    assert exact["unsearched_frontier_nodes"] == exact["pending_complete_leaves"] == 0
    assert exact["whole_original_completion_branch_tree_freshly_independently_math_replayed"]
    assert sha(proofpath) == item["proof_sha256"] == exact["refined_proposal_sha256"]
    assert sha(exactpath) == item["exact_sha256"]
    fresh = replay_refinement(family, proofpath)
    assert fresh == exact
    return {
        "parent_index": expected["parent_index"], "kind": "new-strict-complete-family-refinement",
        "proof_sha256": sha(proofpath), "exact_sha256": sha(exactpath),
        "not_a_strict_geometric_weak_graph_exclusion": True}


def base_gate(stage, lower, base):
    source, weak = parent_gate(stage, lower, True)
    record = read(base / "ACCEPTED/VERIFIED.json")
    assert record["verified"]
    assert record["schema"] == "small-order-full-parent-weak-and-complete-filling-disjoint-adoption-v1"
    assert record["source_sha256"] == sha(ROOT / "small_order_parent_fillings.py")
    assert (record["N"], record["B"], record["parent_weak_graphs"]) == (
        source["N"], source["B"], source["unique_necessary_weak_graphs"])
    assert record["old_weak_lower_report_sha256"] == sha(lower / "ACCEPTED/VERIFIED.json")
    assert record["source_acceptance_sha256"] == sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json")
    assert record["full_parent_partition_complete"]
    assert record["all_actual_current_residual_source_graphs_and_indices_compared"]
    assert record["all_new_completion_family_branches_and_math_freshly_independently_replayed"]
    assert record["all_old_strict_weak_tree_bytes_rebound_old_math_honestly_reused"]
    assert record["old_strict_weak_graphs"] == weak["strictly_excluded"]
    assert record["old_strict_weak_graphs"]+record["new_strict_complete_families"]+record["pending_families"] == record["parent_weak_graphs"]
    for file, field in (
        ("ADDITIONAL-PAYMENTS.jsonl", "additional_payments_sha256"),
        ("PENDING.jsonl", "pending_sha256"), ("AUDITED-JOBS.jsonl", "audited_jobs_sha256")):
        assert sha(base / "ACCEPTED" / file) == record[field]
    assert sha(base / "PARTITION.json") == record["partition_sha256"]
    pipeline = read(base / "PIPELINE-COMPLETED.json")
    terminal = read(base / "AUDIT-TERMINAL.json")
    assert pipeline["actual_all_original_workers_and_independent_parent_audit_terminals_observed"]
    assert pipeline["report_sha256"] == sha(base / "ACCEPTED/VERIFIED.json")
    assert terminal["actual_exit_code"] == 0 and terminal["actual_child_terminal_observed"]
    jobs, paid = 0, 0
    with (base / "ACCEPTED/AUDITED-JOBS.jsonl").open(encoding="ascii") as stream:
        for line in stream:
            audited = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert audited["job"] == jobs
            directory = base / f"batch-{jobs:06}"
            for path, field in (
                (directory / "SUMMARY.json", "worker_report_sha256"),
                (directory / "TERMINAL.json", "terminal_sha256"),
                (base / f"job-{jobs:06}.json", "job_sha256")):
                assert sha(path) == audited[field]
            worker = read(directory / "SUMMARY.json")
            for path, digest in worker["frozen_files"].items():
                assert sha(path) == digest
            paid += sum(item["status"] == "strict-complete-family" for item in worker["outcomes"])
            jobs += 1
    assert paid == record["new_strict_complete_families"]
    return source, record


def main():
    ap = argparse.ArgumentParser()
    for name in ("stage", "lower", "base", "supplements", "controls", "output"):
        ap.add_argument("--"+name, required=True, type=Path)
    args = ap.parse_args()
    stage, lower, base, manifestpath, controls_path, output = (
        getattr(args, key).resolve() for key in ("stage", "lower", "base", "supplements", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (stage, lower, base, manifestpath, controls_path, output))
    assert not output.exists()
    controls = read(controls_path)
    assert controls["verified"] and controls["source_sha256"] == sha(ROOT / "test_small_order_parent_supplements.py")
    assert controls["audit_source_sha256"] == sha(Path(__file__))
    assert len(controls["refusals"]) == 8 and controls["real_whole_family_positive_freshly_replayed"]
    source, old = base_gate(stage, lower, base)
    N, B = source["N"], source["B"]
    manifest = read(manifestpath)
    assert (manifest["N"], manifest["B"]) == (N, B)
    assert manifest["base_report_sha256"] == sha(base / "ACCEPTED/VERIFIED.json")
    additions = {}
    for item in manifest["additions"]:
        pid = item["parent_index"]
        assert type(pid) is int and pid not in additions
        additions[pid] = item
    assert additions
    pendingpath = base / "ACCEPTED/PENDING.jsonl"
    expected = {}
    with pendingpath.open(encoding="ascii") as stream:
        previous = -1
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            pid = row["parent_index"]
            assert type(pid) is int and pid > previous
            previous, expected[pid] = pid, row
    assert len(expected) == old["pending_families"] and set(additions) <= set(expected)
    paid = {}
    for pid in sorted(additions):
        assert Path(additions[pid]["family"]).resolve() == (
            base / f"batch-{expected[pid]['job']:06}" / f"parent-{pid:07}").resolve()
        paid[pid] = supplement(additions[pid], expected[pid], N, B)
        if len(paid) % 10 == 0:
            print("Own-order actual formal-parent new full-family refinements replayed", len(paid),
                  "/", len(additions), flush=True)
    output.mkdir()
    checked, seen, count = 0, set(), 0
    with (output / "ADDITIONAL-PAYMENTS.jsonl").open("x", encoding="ascii") as payments, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as pending:
        for row in rows(stage, source):
            pid = row["id"]
            if pid not in expected:
                continue
            original = expected[pid]
            assert (row["centers"], row["faces"]) == (original["centers"], original["faces"])
            seen.add(pid)
            if pid in paid:
                payments.write(json.dumps(paid[pid], separators=(",", ":"))+"\n")
                checked += 1
            else:
                pending.write(json.dumps(original, separators=(",", ":"))+"\n")
                count += 1
    assert seen == set(expected) and checked == len(paid) and checked+count == old["pending_families"]
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "small-order-formal-complete-parent-strict-refinement-disjoint-adoption-v1",
        "N": N, "B": B, "complete_parent_weak_graphs": old["parent_weak_graphs"],
        "old_strict_weak_graphs": old["old_strict_weak_graphs"],
        "old_strict_complete_families": old["new_strict_complete_families"],
        "new_strict_complete_refined_families": checked, "remaining_pending_families": count,
        "all_old_mathematics_reused_under_checked_complete_parent_and_tree_bytes": True,
        "every_new_whole_completion_tree_freshly_independently_mathematically_replayed": True,
        "every_actual_formal_parent_pending_index_and_source_graph_partitioned_once": True,
        "source_acceptance_sha256": sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json"),
        "base_report_sha256": sha(base / "ACCEPTED/VERIFIED.json"),
        "supplements_manifest_sha256": sha(manifestpath),
        "controls_sha256": sha(controls_path), "source_sha256": sha(Path(__file__)),
        "additional_payments_sha256": sha(output / "ADDITIONAL-PAYMENTS.jsonl"),
        "pending_sha256": sha(output / "PENDING.jsonl"),
        "whole_parent_family_lower_paid": count == 0,
        "source_cover_other_families_and_exact_upper_global_synthesis_still_required": True,
        "global_optimality_proved": False})


if __name__ == "__main__":
    main()
