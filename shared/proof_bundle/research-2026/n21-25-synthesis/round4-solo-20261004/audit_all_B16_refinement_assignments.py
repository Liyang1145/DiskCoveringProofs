"""Exact disjoint assignment coverage only; unfinished batches remain unpaid."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    stage = ROOT / "n25-B16-origin-slab0-all11179-residual-reboot-20261005-v1"
    source_path, snapshot_path = stage / "FILLINGS/VERIFIED.json", stage / "ALL-PENDING-SNAPSHOT.json"
    source, terminal, snapshot = map(read, (
        source_path, stage / "FILLINGS-TERMINAL.json", snapshot_path))
    assert source["verified"] and source["schema"] == "finite-discovery-linked-filling-payments-v1"
    assert source["source_sha256"] == sha(ROOT / "pay_finite_discovery_fillings.py")
    assert terminal["native_or_python_terminal_observed"] and terminal["actual_exit_code"] == 0
    assert terminal["source_sha256"] == source["source_sha256"]
    assert terminal["output_log_sha256"] == sha(stage / "FILLINGS-OUTPUT.log")
    assert source["source_snapshot_sha256"] == sha(snapshot_path)
    assert (source["N"], source["B"], snapshot["N"], snapshot["B"]) == (25, 16, 25, 16)
    assert source["finite_pending_samples_processed_once"] == len(source["outcomes"]) == 8049
    by_sample = {row["sample"]: row for row in source["outcomes"]}
    assert len(by_sample) == len(source["outcomes"])
    assert set(source["counts"]) == {"pending", "strictly-paid-complete-filling-family"}
    assert all(row["unsearched_frontier_nodes"] == 0 for row in source["outcomes"])
    pending = {sample for sample, row in by_sample.items() if row["status"] == "pending"}
    assert len(pending) == source["remaining_unpaid_families"] == 7475
    directories = [
        "n25-B16-all8049-completed-pending-snapshot256-force31-20261005-v1",
        "n25-B16-all8049-completed-pending-next512-force31-20261005-v1",
        "n25-B16-all8049-completed-pending-next1024-force31-20261005-v1",
        *[f"n25-B16-all8049-completed-pending-wave{wave}-force31-20261005-v1" for wave in range(4, 9)],
        "n25-B16-all8049-final-unassigned-force31-20261005-v1",
    ]
    assigned, batches, files = set(), [], {}
    stage_inputs = stage / "FILLINGS/INPUT-BINDINGS.json"
    for name in directories:
        path = ROOT / name / "INPUT-SNAPSHOT.json"
        frozen = read(path)
        assert frozen["source_discovery_snapshot_sha256"] == sha(snapshot_path)
        assert frozen["source_stage_input_bindings_sha256"] == sha(stage_inputs)
        assert frozen["force_limit"] == 31
        selected = frozen["selected_completed_pending_families"]
        assert selected
        samples = [row["sample"] for row in selected]
        assert len(samples) == len(set(samples)) and not assigned.intersection(samples)
        assert set(samples) <= pending
        for row in selected:
            sample = row["sample"]
            family = ROOT / row["family_relative_to_round4"]
            assert family == stage / f"FILLINGS/sample-{sample:07}"
            original_status = read(family / "STATUS.json")
            assert original_status == by_sample[sample]
            graph = snapshot["weak_graphs"][sample]
            assert (original_status["centers"], original_status["faces"]) == (graph["centers"], graph["faces"])
            for key, filename in (
                ("status_sha256", "STATUS.json"), ("proposal_sha256", "PROPOSAL.json"),
                ("exact_sha256", "EXACT.json"), ("successful_replay_terminal_sha256", "REPLAY-TERMINAL.json"),
            ):
                assert row[key] == sha(family / filename)
            original_exact = read(family / "EXACT.json")
            assert original_exact["verified"] and original_exact["pending_complete_leaves"] > 0
            assert original_exact["unsearched_frontier_nodes"] == 0
            actual_terminal = read(family / "REPLAY-TERMINAL.json")
            assert actual_terminal["actual_exit_code"] == 0 and actual_terminal["independent_process_terminal_observed"]
        assigned.update(samples)
        batches.append({"directory": name, "assigned_samples": len(samples),
                        "input_snapshot_sha256": sha(path), "not_a_batch_payment_claim": True})
        bind(files, path)
    assert assigned == pending
    assert sum(row["assigned_samples"] for row in batches) == 7475
    assert [row["assigned_samples"] for row in batches] == [256, 512, 1024, 1024, 1024, 1024, 1024, 799, 788]
    for path in (Path(__file__), source_path, snapshot_path, stage_inputs,
                 stage / "FILLINGS-TERMINAL.json", stage / "FILLINGS-OUTPUT.log"):
        bind(files, path)
    unchanged(files)
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "finite-B16-completed-pending-refinement-assignment-partition-v1",
        "N": 25, "B": 16, "source_processed_families": 8049,
        "source_directly_paid_families": 574, "source_pending_families": 7475,
        "assigned_pending_families": len(assigned), "unassigned_pending_families": 0,
        "all_pending_source_families_assigned_exactly_once": True,
        "all_assignments_bound_to_completed_independent_original_replays": True,
        "batches": batches,
        "assignment_is_not_proof_payment_or_batch_completion": True,
        "final_all_positive_payments_and_whole_slab_overlap_audit_still_required": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "not_a_complete_competitor_family_or_union": True, "global_optimality_proved": False,
    })
    print("B16 exact pending assignment coverage PASS:", len(assigned),
          "families assigned once in nine disjoint batches; assignments are not payments", flush=True)


if __name__ == "__main__":
    main()
