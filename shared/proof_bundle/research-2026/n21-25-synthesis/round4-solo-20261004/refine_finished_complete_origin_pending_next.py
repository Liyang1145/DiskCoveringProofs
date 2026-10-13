"""One-shot finer trees for finished pending families not already selected.

This successor keeps the original refinement adapter and all active kernels
unchanged. Prior immutable refinement selections are excluded by parent id.
"""
from pathlib import Path
import argparse
import os
import subprocess
import sys
import json

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish, unchanged

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("snapshot", "stage", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--prior-refinement", type=Path, action="append", default=[])
    ap.add_argument("--force-limit", type=int, default=127)
    args = ap.parse_args()
    snapshotpath, stage, output = (getattr(args, name).resolve()
                                   for name in ("snapshot", "stage", "output"))
    assert all(path.is_relative_to(ROOT) for path in (snapshotpath, stage, output))
    assert not output.exists() and 31 < args.force_limit <= 1001
    snapshot, inputs = read(snapshotpath), read(stage / "INPUT-BINDINGS.json")
    assert snapshot["schema"] == "all-pending-complete-origin-parent-exact-graph-snapshot-v1"
    assert snapshot["source_sha256"] == sha(ROOT / "snapshot_complete_origin_pending.py")
    assert snapshot["all_full_parent_pending_rows_frozen_once"]
    assert inputs["snapshot_sha256"] == sha(snapshotpath)
    for path, digest in {**snapshot["frozen_files"], **inputs["frozen_files"]}.items():
        assert sha(path) == digest
    excluded = set()
    frozen = {}
    for priorpath in args.prior_refinement:
        priorpath = priorpath.resolve()
        assert priorpath.is_relative_to(ROOT)
        prior = read(priorpath)
        assert prior["verified"] and prior["schema"] == "finished-complete-origin-pending-leaf-refinement-results-v1"
        assert prior["source_complete_parent_snapshot_sha256"] == sha(snapshotpath)
        assert prior["source_sha256"] in (
            sha(ROOT / "refine_finished_complete_origin_pending.py"), sha(Path(__file__)))
        for path, digest in prior["frozen_files"].items():
            assert sha(path) == digest
        assert len({row["parent_index"] for row in prior["outcomes"]}) == len(prior["outcomes"])
        excluded.update(row["parent_index"] for row in prior["outcomes"])
        frozen[str(priorpath)] = sha(priorpath)
    leafcontrolpath = ROOT / "n25-linked-leaf-refinement-controls-20261005-v1/VERIFIED.json"
    controls = read(leafcontrolpath)
    assert controls["verified"] and controls["schema"] == "linked-leaf-only-refinement-controls-v1"
    assert controls["known_exact_N25_attaining_full_type_explicitly_retained_unpaid"]
    unchanged(controls["files_relative_to_workspace"])
    N, B = snapshot["N"], snapshot["B"]
    assert N == 25 and B in (14, 15, 16, 17)
    selected, seen = [], set()
    with (stage / "COMPLETED-BATCHES.jsonl").open(encoding="ascii") as stream:
        for line in stream:
            if not line.endswith("\n"):
                break
            descriptor = json.loads(line, object_pairs_hook=no_duplicate_keys)
            first = descriptor["first"]
            assert first not in seen
            seen.add(first)
            workerpath = stage / f"batch-{first//inputs['worker_batch_size']:06}/SUMMARY.json"
            assert sha(workerpath) == descriptor["worker_report_sha256"]
            worker = read(workerpath)
            assert worker["schema"] == "complete-parent-pending-filling-worker-v1"
            assert worker["source_sha256"] == sha(ROOT / "pay_complete_origin_pending.py")
            assert worker["snapshot_sha256"] == sha(snapshotpath)
            assert worker["first"] == first and worker["count"] == descriptor["count"] == len(worker["outcomes"])
            for local, status in enumerate(worker["outcomes"]):
                graph = snapshot["graphs"][first+local]
                assert (status["parent_index"], status["centers"], status["faces"]) == (
                    graph["parent_index"], graph["centers"], graph["faces"])
                if status["parent_index"] in excluded:
                    continue
                if status["status"] != "pending" or status.get("unsearched_frontier_nodes") != 0:
                    continue
                if status.get("pending_complete_leaves", 0) <= 0:
                    continue
                family = workerpath.parent / f"parent-{status['parent_index']:07}"
                originalpath, exactpath, earlierpath = (
                    family / "PROPOSAL.json", family / "EXACT.json", family / "REFINEMENT/EXACT.json")
                original, accepted, earlier = map(read, (originalpath, exactpath, earlierpath))
                assert accepted["verified"] and earlier["verified"] and earlier["whole_tree_fresh_exact_replayed"]
                assert accepted["source_sha256"] == sha(ROOT / "replay_linked_general_collar.py")
                assert earlier["source_sha256"] == sha(ROOT / "replay_refined_linked_leaves.py")
                assert earlier["pending_complete_leaves"] == status["pending_complete_leaves"]
                assert earlier["unsearched_frontier_nodes"] == accepted["unsearched_frontier_nodes"] == 0
                assert not earlier["all_full_simple_disk_completions_strictly_paid"]
                assert (original["N"], original["B"], original["collar_centers"], original["collar_faces"]) == (
                    N, B, graph["centers"], graph["faces"])
                unchanged(accepted["files_relative_to_workspace"])
                unchanged(earlier["files_relative_to_workspace"])
                selected.append({
                    "parent_index": status["parent_index"], "family": str(family),
                    "source_worker_sha256": sha(workerpath), "centers": graph["centers"], "faces": graph["faces"],
                    "earlier_force31_exact_sha256": sha(earlierpath),
                })
                for path in (workerpath, family / "INPUT-COLLAR.json", family / "STATUS.json",
                             originalpath, exactpath, earlierpath, family / "REFINEMENT/REFINED.json"):
                    frozen[str(path)] = sha(path)
    assert selected and len(selected) <= 1024
    for path in (Path(__file__).resolve(), snapshotpath, stage / "INPUT-BINDINGS.json",
                 leafcontrolpath, ROOT / "refine_linked_collar_leaves.py",
                 ROOT / "replay_refined_linked_leaves.py", ROOT / "linked_general_collar_kernel.py"):
        frozen[str(path)] = sha(path)
    output.mkdir()
    publish(output / "INPUT-SNAPSHOT.json", {
        "schema": "finished-complete-origin-pending-leaf-refinement-snapshot-v1",
        "N": N, "B": B, "selected": selected, "frozen_files": frozen,
        "source_complete_parent_snapshot_sha256": sha(snapshotpath),
        "force_limit": args.force_limit, "excluded_prior_parent_indices": sorted(excluded),
        "only_finished_pending_no_frontier_families_selected": True,
        "not_a_restart_of_active_worker_or_topology_tree": True,
        "global_optimality_proved": False,
    })
    outcomes = []
    for row in selected:
        family = Path(row["family"])
        directory = output / f"parent-{row['parent_index']:07}"
        directory.mkdir()
        proofpath, exactpath = directory / "REFINED.json", directory / "EXACT.json"
        status = {"parent_index": row["parent_index"], "status": "pending"}
        for label, script, arguments in (
            ("PROPOSE", ROOT / "refine_linked_collar_leaves.py", [
                "--family", family, "--output", proofpath, "--force-limit", args.force_limit]),
            ("REPLAY", ROOT / "replay_refined_linked_leaves.py", [
                "--family", family, "--refined", proofpath, "--output", exactpath]),
        ):
            with (directory / (label+"-STDOUT.log")).open("xb") as stdout, \
                    (directory / (label+"-STDERR.log")).open("xb") as stderr:
                process = subprocess.Popen(
                    [sys.executable, "-u", str(script), *map(str, arguments)],
                    stdout=stdout, stderr=stderr, cwd=str(ROOT),
                    env=dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1"),
                    creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
                code = process.wait()
            publish(directory / (label+"-TERMINAL.json"), {
                "actual_exit_code": code, "child_pid": process.pid,
                "source_sha256": sha(script), "process_terminal_observed": True,
            })
            if code != 0:
                status["reason"] = label+" process failed; not paid"
                break
        else:
            accepted = read(exactpath)
            assert accepted["verified"] and accepted["whole_tree_fresh_exact_replayed"]
            assert accepted["source_sha256"] == sha(ROOT / "replay_refined_linked_leaves.py")
            assert (accepted["N"], accepted["B"], accepted["collar_centers"], accepted["collar_faces"]) == (
                N, B, row["centers"], row["faces"])
            unchanged(accepted["files_relative_to_workspace"])
            status.update(
                status=("strict-complete-filling-family" if accepted["all_full_simple_disk_completions_strictly_paid"]
                        else "pending"),
                pending_complete_leaves=accepted["pending_complete_leaves"],
                unsearched_frontier_nodes=accepted["unsearched_frontier_nodes"],
                proof_sha256=sha(proofpath), exact_sha256=sha(exactpath))
        for path, digest in frozen.items():
            assert sha(path) == digest
        publish(directory / "STATUS.json", status)
        outcomes.append(status)
        print("Next disjoint finished-pending refinement", row["parent_index"],
              status["status"], status.get("pending_complete_leaves"), flush=True)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "finished-complete-origin-pending-leaf-refinement-results-v1",
        "N": N, "B": B, "selected_families": len(selected), "outcomes": outcomes,
        "strict_families": sum(row["status"] == "strict-complete-filling-family" for row in outcomes),
        "pending_families": sum(row["status"] == "pending" for row in outcomes),
        "source_complete_parent_snapshot_sha256": sha(snapshotpath),
        "input_snapshot_sha256": sha(output / "INPUT-SNAPSHOT.json"), "frozen_files": frozen,
        "only_original_FULL_PENDING_leaves_changed": True,
        "all_old_positive_nodes_and_topological_child_lists_unchanged": True,
        "excluded_prior_parent_indices": sorted(excluded),
        "not_yet_full_parent_payment_merge": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
