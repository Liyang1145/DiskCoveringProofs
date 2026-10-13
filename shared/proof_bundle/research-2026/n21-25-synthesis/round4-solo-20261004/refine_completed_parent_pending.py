"""Deepen only pending families from actually completed original worker batches.

An observed subset of completed batches is not a completed scheduler or a
full-source payment. Original workers, summaries and proofs stay unchanged.
"""
from pathlib import Path
from collections import Counter
import argparse
import json
import os
import subprocess
import sys

from n25_outer_search import read, publish
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def run(command, directory, name):
    with (directory / (name+"-STDOUT.log")).open("xb") as stdout, \
            (directory / (name+"-STDERR.log")).open("xb") as stderr:
        process = subprocess.Popen(
            list(map(str, command)), cwd=str(ROOT), stdout=stdout, stderr=stderr,
            env=dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1"),
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(directory / (name+"-TERMINAL.json"), {
        "child_pid": process.pid, "actual_exit_code": code,
        "independent_process_terminal_observed": True,
        "command": list(map(str, command)), "source_sha256": sha(Path(__file__)),
    })
    assert code == 0, (name, code)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--force-limit", type=int, default=511)
    ap.add_argument("--skip-parent", type=int, nargs="*", default=[])
    args = ap.parse_args()
    stage, output = args.stage.resolve(), args.output.resolve()
    assert stage.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    assert 31 < args.force_limit <= 10001
    assert len(args.skip_parent) == len(set(args.skip_parent))
    inputs = read(stage / "INPUT-BINDINGS.json")
    N, B = inputs["N"], inputs["B"]
    assert N == 25 and B in (16, 17)
    batchsize = inputs.get("worker_batch_size", 128)
    descriptorrows = []
    with (stage / "COMPLETED-BATCHES.jsonl").open(encoding="ascii") as stream:
        for line in stream:
            if not line.endswith("\n"):
                # A concurrent writer's incomplete final line is not observed
                # as a completed descriptor and is not frozen into this scope.
                break
            descriptorrows.append(json.loads(line, object_pairs_hook=no_duplicate_keys))
    assert descriptorrows
    frozen = {str(path): sha(path) for path in (
        Path(__file__), stage / "INPUT-BINDINGS.json",
        ROOT / "pay_complete_origin_pending.py", ROOT / "refine_linked_collar_leaves.py",
        ROOT / "replay_refined_linked_leaves.py", ROOT / "linked_general_collar_kernel.py")}
    selected, seen, allpending = [], set(), set()
    for descriptor in descriptorrows:
        ordinal = descriptor.get("job", descriptor["first"]//batchsize)
        assert type(ordinal) is int and ordinal >= 0 and ordinal not in seen
        seen.add(ordinal)
        workerpath = stage / f"batch-{ordinal:06}/SUMMARY.json"
        assert sha(workerpath) == descriptor["worker_report_sha256"]
        worker = read(workerpath)
        assert worker["schema"] == "complete-parent-pending-filling-worker-v1"
        assert worker["source_sha256"] == sha(ROOT / "pay_complete_origin_pending.py")
        assert (worker["N"], worker["B"]) == (N, B)
        assert (worker["first"], worker["count"]) == (descriptor["first"], descriptor["count"])
        assert Counter(row["status"] for row in worker["outcomes"]) == descriptor["counts"]
        assert len(worker["outcomes"]) == descriptor["count"]
        for path, digest in worker["frozen_files"].items():
            assert sha(path) == digest
            assert path not in frozen or frozen[path] == digest
            frozen[path] = digest
        frozen[str(workerpath)] = sha(workerpath)
        for outcome in worker["outcomes"]:
            if outcome["status"] != "pending":
                assert outcome["status"] == "strict-complete-filling-family"
                continue
            pid = outcome["parent_index"]
            assert type(pid) is int and pid not in allpending
            allpending.add(pid)
            family = stage / f"batch-{ordinal:06}/parent-{pid:07}"
            accepted = read(family / "EXACT.json")
            assert accepted["verified"] and accepted["unsearched_frontier_nodes"] == 0
            assert accepted["pending_complete_leaves"] > 0
            if pid in args.skip_parent:
                continue
            selected.append({
                "parent_index": pid, "family": str(family), "worker_report_sha256": sha(workerpath),
                "observed_original_completed_descriptor": descriptor,
            })
            for name in ("INPUT-COLLAR.json", "PROPOSAL.json", "EXACT.json"):
                frozen[str(family / name)] = sha(family / name)
    assert set(args.skip_parent).issubset(allpending)
    assert selected
    output.mkdir()
    publish(output / "SCOPED-INPUTS.json", {
        "N": N, "B": B, "observed_completed_batches": len(descriptorrows),
        "observed_pending_families": len(allpending), "selected_families": selected,
        "skipped_explicit_parent_indices": args.skip_parent,
        "mutable_completed_batches_file_not_used_as_a_final_proof_identity": True,
        "frozen_actual_worker_reports_and_original_families": frozen,
        "not_an_entire_scheduler_or_full_parent_payment": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    outcomes = []
    for selectedrow in selected:
        pid, family = selectedrow["parent_index"], Path(selectedrow["family"])
        proofpath, exactpath = output / f"p{pid}-PROOF.json", output / f"p{pid}-EXACT.json"
        run([sys.executable, "-u", ROOT / "refine_linked_collar_leaves.py",
             "--family", family, "--output", proofpath, "--force-limit", args.force_limit],
            output, f"p{pid}-PROPOSE")
        run([sys.executable, "-u", ROOT / "replay_refined_linked_leaves.py",
             "--family", family, "--refined", proofpath, "--output", exactpath],
            output, f"p{pid}-REPLAY")
        accepted = read(exactpath)
        assert accepted["verified"]
        closed = accepted["all_full_simple_disk_completions_strictly_paid"]
        outcomes.append({
            **selectedrow, "whole_family_strictly_closed": closed,
            "proof_path": str(proofpath), "exact_path": str(exactpath),
            "proof_sha256": sha(proofpath), "exact_sha256": sha(exactpath),
            "pending_complete_leaves": accepted["pending_complete_leaves"],
            "unsearched_frontier_nodes": accepted["unsearched_frontier_nodes"],
        })
        print("Completed-batch deep family independent replay", pid, "whole closed", closed,
              len(outcomes), "/", len(selected), flush=True)
    for path, digest in frozen.items():
        assert sha(path) == digest
    publish(output / "SUMMARY.json", {
        "N": N, "B": B, "outcomes": outcomes, "selected_families": len(selected),
        "whole_families_strictly_closed": sum(row["whole_family_strictly_closed"] for row in outcomes),
        "all_independent_child_terminals_actually_observed": True, "frozen_files": frozen,
        "complete_source_payment_adoption_not_performed_here": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
