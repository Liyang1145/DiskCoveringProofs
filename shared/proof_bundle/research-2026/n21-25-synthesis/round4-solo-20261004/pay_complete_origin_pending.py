"""Bounded subprocess batches of whole-filling proofs for a complete parent.

The original topological branch tree is produced with force limit 1; only
completed pending full leaves are subsequently refined by the frozen programs.
Each positive result requires its own independent accepting process.
"""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
from collections import Counter
import argparse
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish, unchanged

assert __debug__


def invoke(script, arguments, directory, label, frozen):
    assert sha(script) == frozen[str(script)]
    env = dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1")
    with (directory / (label+"-STDOUT.log")).open("xb") as stdout, \
            (directory / (label+"-STDERR.log")).open("xb") as stderr:
        process = subprocess.Popen([sys.executable, "-u", str(script), *map(str, arguments)],
                                   cwd=str(ROOT), stdout=stdout, stderr=stderr, env=env,
                                   creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(directory / (label+"-TERMINAL.json"), {
        "actual_exit_code": code, "child_pid": process.pid,
        "source_sha256": frozen[str(script)], "real_process_terminal_observed": True,
    })
    return code


def gate(snapshotpath, controls):
    snapshot, tested = read(snapshotpath), read(controls)
    assert snapshot["schema"] == "all-pending-complete-origin-parent-exact-graph-snapshot-v1"
    assert snapshot["source_sha256"] == sha(ROOT / "snapshot_complete_origin_pending.py")
    assert snapshot["all_full_parent_pending_rows_frozen_once"]
    assert snapshot["every_pending_parent_row_compared_against_full_catalog"]
    assert snapshot["selected_pending_graphs"] == len(snapshot["graphs"])
    for path, digest in snapshot["frozen_files"].items():
        assert sha(path) == digest
    assert tested["verified"] and tested["schema"] == "linked-general-collar-filling-controls-v1"
    assert tested["known_attaining_candidate_not_strictly_paid"]
    for field, filename in (
        ("source_sha256", "test_linked_general_collar.py"), ("kernel_sha256", "linked_general_collar_kernel.py"),
        ("provider_sha256", "general_collar_filling_linked.py"),
        ("proposal_source_sha256", "prove_linked_general_collar.py"),
        ("replay_source_sha256", "replay_linked_general_collar.py"),
        ("source_induction_sha256", "GENERAL-COLLAR-FILLING-SOURCE.md")):
        assert tested[field] == sha(ROOT / filename)
    unchanged(tested["files_relative_to_workspace"])
    leafcontrolpath = ROOT / "n25-linked-leaf-refinement-controls-20261005-v1/VERIFIED.json"
    leafcontrols = read(leafcontrolpath)
    assert leafcontrols["verified"] and leafcontrols["schema"] == "linked-leaf-only-refinement-controls-v1"
    assert leafcontrols["known_exact_N25_attaining_full_type_explicitly_retained_unpaid"]
    unchanged(leafcontrols["files_relative_to_workspace"])
    sourcecontrolpath = ROOT / "complete-origin-filling-parent-source-controls-20261005-v1/VERIFIED.json"
    sourcecontrols = read(sourcecontrolpath)
    assert sourcecontrols["verified"]
    assert sourcecontrols["schema"] == "complete-origin-filling-parent-source-binding-controls-v1"
    assert len(sourcecontrols["negative_controls_rejected"]) == 10
    for field, filename in (
        ("source_sha256", "test_complete_origin_filling_sources.py"),
        ("snapshot_source_sha256", "snapshot_complete_origin_pending.py"),
        ("worker_source_sha256", "pay_complete_origin_pending.py"),
        ("merge_source_sha256", "audit_complete_origin_fillings.py")):
        assert sourcecontrols[field] == sha(ROOT / filename)
    paths = [
        snapshotpath, controls, leafcontrolpath, sourcecontrolpath, Path(__file__).resolve(),
        ROOT / "prove_linked_general_collar.py", ROOT / "replay_linked_general_collar.py",
        ROOT / "linked_general_collar_kernel.py", ROOT / "general_collar_filling.py",
        ROOT / "general_collar_filling_linked.py", ROOT / "refine_linked_collar_leaves.py",
        ROOT / "replay_refined_linked_leaves.py", ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md",
        ROOT / "audit_complete_origin_fillings.py",
        HIGH / "probe_groups.py", HIGH / "exact_graph.py",
        ROOT.parent / "evidence/core-reduction/constants/n25.json",
    ]
    return snapshot, {str(path): sha(path) for path in paths}


def worker(snapshotpath, controls, output, first, count, limit, force_limit):
    snapshot, frozen = gate(snapshotpath, controls)
    from linked_general_collar_kernel import start_states
    from prove_linked_general_collar import propose
    N, B = snapshot["N"], snapshot["B"]
    assert N == 25 and B in (14, 15, 16, 17)
    selected = snapshot["graphs"][first:first+count]
    assert selected and not output.exists()
    output.mkdir()
    constantspath = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constantspath)
    assert constants["verified"] and constants["N"] == N
    outcomes = []
    for row in selected:
        index = row["parent_index"]
        directory = output / f"parent-{index:07}"
        directory.mkdir()
        collar = {"N": N, "B": B, "centers": row["centers"], "faces": row["faces"],
                  "complete_parent_index": index, "source_snapshot_sha256": sha(snapshotpath)}
        status = {"parent_index": index, "status": "pending", "centers": row["centers"],
                  "faces": row["faces"], "not_a_standalone_geometric_weak_graph_exclusion": True}
        try:
            start_states(N, B, row["centers"], row["faces"])
        except AssertionError as error:
            status["reason"] = "unhandled source topology: "+str(error)
        else:
            collarpath, proposalpath, exactpath = (directory / name for name in
                                                  ("INPUT-COLLAR.json", "PROPOSAL.json", "EXACT.json"))
            publish(collarpath, collar)
            proposal = propose(collar, constants, limit, 1)
            proposal.update(
                source_collar_sha256=sha(collarpath), constants_sha256=sha(constantspath),
                kernel_sha256=sha(ROOT / "linked_general_collar_kernel.py"),
                source_sha256=sha(ROOT / "prove_linked_general_collar.py"),
                whole_family_payment_requires_independent_replay=True, global_optimality_proved=False)
            publish(proposalpath, proposal)
            code = invoke(ROOT / "replay_linked_general_collar.py", [
                "--collar", collarpath, "--proposal", proposalpath, "--output", exactpath],
                directory, "REPLAY", frozen)
            if code == 0:
                accepted = read(exactpath)
                assert accepted["verified"]
                unchanged(accepted["files_relative_to_workspace"])
                status.update(pending_complete_leaves=accepted["pending_complete_leaves"],
                              unsearched_frontier_nodes=accepted["unsearched_frontier_nodes"])
                if accepted["all_full_simple_disk_completions_strictly_paid"]:
                    status.update(status="strict-complete-filling-family",
                                  proof_relative_to_stage=proposalpath.relative_to(output).as_posix(),
                                  exact_relative_to_stage=exactpath.relative_to(output).as_posix(),
                                  proof_sha256=sha(proposalpath), exact_sha256=sha(exactpath))
                elif accepted["unsearched_frontier_nodes"] == 0:
                    refinement = directory / "REFINEMENT"
                    refinement.mkdir()
                    refinedpath, refinedexact = refinement / "REFINED.json", refinement / "EXACT.json"
                    code = invoke(ROOT / "refine_linked_collar_leaves.py", [
                        "--family", directory, "--output", refinedpath, "--force-limit", force_limit],
                        refinement, "PROPOSE", frozen)
                    if code == 0:
                        code = invoke(ROOT / "replay_refined_linked_leaves.py", [
                            "--family", directory, "--refined", refinedpath, "--output", refinedexact],
                            refinement, "REPLAY", frozen)
                    if code == 0:
                        result = read(refinedexact)
                        assert result["verified"] and result["whole_tree_fresh_exact_replayed"]
                        unchanged(result["files_relative_to_workspace"])
                        status.update(pending_complete_leaves=result["pending_complete_leaves"],
                                      unsearched_frontier_nodes=result["unsearched_frontier_nodes"])
                        if result["all_full_simple_disk_completions_strictly_paid"]:
                            status.update(status="strict-complete-filling-family",
                                          proof_relative_to_stage=refinedpath.relative_to(output).as_posix(),
                                          exact_relative_to_stage=refinedexact.relative_to(output).as_posix(),
                                          proof_sha256=sha(refinedpath), exact_sha256=sha(refinedexact))
                if code != 0:
                    status["reason"] = "a refine/replay process failed; not paid"
            else:
                status["reason"] = "exact filling replay failed; not paid"
        for path, digest in frozen.items():
            assert sha(path) == digest
        publish(directory / "STATUS.json", status)
        outcomes.append(status)
        print("Complete-parent fixed filling", index, status["status"],
              status.get("pending_complete_leaves"), status.get("unsearched_frontier_nodes"), flush=True)
    publish(output / "SUMMARY.json", {
        "schema": "complete-parent-pending-filling-worker-v1",
        "N": N, "B": B, "snapshot_sha256": sha(snapshotpath),
        "first": first, "count": len(selected), "outcomes": outcomes,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "individual_family_replays_not_yet_full_parent_union_payments": True,
        "global_optimality_proved": False,
    })


def main():
    ap = argparse.ArgumentParser()
    for name in ("snapshot", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--batch-size", type=int, default=128)
    ap.add_argument("--limit", type=int, default=10000)
    ap.add_argument("--force-limit", type=int, default=31)
    ap.add_argument("--worker-first", type=int)
    ap.add_argument("--worker-count", type=int)
    args = ap.parse_args()
    snapshotpath, controls, output = (getattr(args, name).resolve()
                                     for name in ("snapshot", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (snapshotpath, controls, output))
    assert not output.exists() and 1 <= args.limit <= 100000 and 1 <= args.force_limit <= 1001
    if args.worker_first is not None:
        assert args.worker_first >= 0 and args.worker_count is not None and 1 <= args.worker_count <= 1024
        worker(snapshotpath, controls, output, args.worker_first, args.worker_count, args.limit, args.force_limit)
        return
    assert 1 <= args.workers <= 8 and 1 <= args.batch_size <= 1024
    snapshot, frozen = gate(snapshotpath, controls)
    total = snapshot["selected_pending_graphs"]
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "N": snapshot["N"], "B": snapshot["B"], "pending_graphs": total,
        "snapshot_sha256": sha(snapshotpath), "frozen_files": frozen,
        "worker_batch_size": args.batch_size, "workers": args.workers,
        "independent_family_replays_require_full_parent_payment_merge": True,
        "global_optimality_proved": False,
    })

    def job(first):
        stage = output / f"batch-{first//args.batch_size:06}"
        logs = output / f"logs-{first//args.batch_size:06}"
        logs.mkdir()
        count = min(args.batch_size, total-first)
        code = invoke(Path(__file__).resolve(), [
            "--snapshot", snapshotpath, "--controls", controls, "--output", stage,
            "--worker-first", first, "--worker-count", count,
            "--limit", args.limit, "--force-limit", args.force_limit], logs, "WORKER", frozen)
        assert code == 0, ("filling worker failed; prior outputs preserved", first)
        reportpath = stage / "SUMMARY.json"
        result = read(reportpath)
        assert result["snapshot_sha256"] == sha(snapshotpath) and result["count"] == count
        return {"first": first, "count": count, "worker_report_sha256": sha(reportpath),
                "counts": dict(Counter(row["status"] for row in result["outcomes"]))}

    todo = iter(range(0, total, args.batch_size))
    completed = 0
    counts = Counter()
    with (output / "COMPLETED-BATCHES.jsonl").open("x", encoding="ascii") as ledger:
        with ThreadPoolExecutor(max_workers=args.workers) as executor:
            active = {executor.submit(job, first) for first in
                      [next(todo) for _ in range(min(args.workers, (total+args.batch_size-1)//args.batch_size))]}
            while active:
                done, active = wait(active, return_when=FIRST_COMPLETED)
                results = [future.result() for future in done]
                for result in results:
                    ledger.write(json.dumps(result, separators=(",", ":"))+"\n")
                    ledger.flush()
                    completed += result["count"]
                    counts.update(result["counts"])
                    print("Complete-parent filling stage processed", completed, "/", total, dict(counts), flush=True)
                    first = next(todo, None)
                    if first is not None:
                        active.add(executor.submit(job, first))
    assert completed == total
    publish(output / "SUMMARY.json", {
        "scheduler_completed": True, "schema": "complete-parent-pending-filling-jobs-v1",
        "N": snapshot["N"], "B": snapshot["B"], "snapshot_sha256": sha(snapshotpath),
        "processed_graphs": completed, "counts": dict(counts),
        "completed_batches_sha256": sha(output / "COMPLETED-BATCHES.jsonl"),
        "source_sha256": sha(Path(__file__)),
        "individual_replays_not_a_fresh_full_parent_payment_merge": True,
        "global_optimality_proved": False,
    })
    code = invoke(ROOT / "audit_complete_origin_fillings.py", [
        "--snapshot", snapshotpath, "--stage", output, "--controls", controls,
        "--output", output / "COMPLETE-PAYMENT-AUDIT"], output, "FULL-PARENT-AUDIT", frozen)
    assert code == 0, "fresh full-parent weak/filling audit failed; no merged payment claim"


if __name__ == "__main__":
    main()
