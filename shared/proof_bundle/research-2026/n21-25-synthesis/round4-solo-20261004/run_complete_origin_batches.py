"""One-shot bounded arithmetic jobs followed by the frozen full-parent audit.

The worker processes are numerical proposal / exact replay programs, not agents.
Nothing in a native search, prior certificate, or accepting program is edited.
The scheduler itself is not a mathematical accepting path.
"""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from batch_origin_collar import parent_gate

assert __debug__


def invoke(script, arguments, directory, label, expected_hashes):
    assert sha(script) == expected_hashes[str(script)]
    env = dict(os.environ)
    for key in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS",
                "NUMEXPR_NUM_THREADS", "BLIS_NUM_THREADS"):
        env[key] = "1"
    command = [sys.executable, "-u", str(script), *map(str, arguments)]
    started = time.monotonic()
    stdoutpath, stderrpath = directory / (label+"-STDOUT.log"), directory / (label+"-STDERR.log")
    with stdoutpath.open("xb") as stdout, stderrpath.open("xb") as stderr:
        process = subprocess.Popen(
            command, cwd=str(ROOT), stdout=stdout, stderr=stderr, env=env,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(directory / (label+"-TERMINAL.json"), {
        "actual_exit_code": code, "child_pid": process.pid,
        "source_sha256": expected_hashes[str(script)], "command": command,
        "stdout_sha256": sha(stdoutpath), "stderr_sha256": sha(stderrpath),
        "seconds": time.monotonic()-started,
        "exit_zero_is_not_a_mathematical_payment": True,
    })
    assert code == 0, (label, code, str(stderrpath))
    for path, digest in expected_hashes.items():
        assert sha(path) == digest, ("frozen program/input changed", path)


def main():
    ap = argparse.ArgumentParser()
    for name in ("manifest", "terminal", "union", "partition", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--workers", type=int, default=4)
    args = ap.parse_args()
    assert 1 <= args.workers <= 8
    manifest, terminal, unionpath, partitionpath, output = (
        getattr(args, name).resolve()
        for name in ("manifest", "terminal", "union", "partition", "output"))
    assert output.is_relative_to(ROOT) and not output.exists()
    assert partitionpath.parent.is_relative_to(ROOT)
    union, catalogpath, bindingpath = parent_gate(manifest, terminal, unionpath)
    report = read(partitionpath)
    assert report["verified"] and report["schema"] == "complete-collar-union-bounded-partition-v1"
    assert (report["N"], report["B"], report["weak_graph_count"]) == (
        union["N"], union["B"], union["unique_necessary_weak_graphs"])
    assert report["complete_parent_union_partitioned_once"]
    assert report["source_sha256"] == sha(ROOT / "batch_origin_collar.py")
    for key, path in (
        ("manifest_sha256", manifest), ("native_terminal_sha256", terminal),
        ("parent_union_report_sha256", unionpath), ("parent_catalog_sha256", catalogpath),
        ("parent_bindings_sha256", bindingpath)):
        assert report[key] == sha(path)
    descriptorpath = partitionpath.parent / report["descriptor_file"]
    assert descriptorpath == partitionpath.parent / "BATCHES.jsonl"
    assert sha(descriptorpath) == report["descriptor_sha256"]
    descriptors = []
    count = 0
    with descriptorpath.open(encoding="ascii") as stream:
        for line in stream:
            descriptor = json.loads(line, object_pairs_hook=no_duplicate_keys)
            index = len(descriptors)
            assert descriptor["batch"] == index and descriptor["first"] == count
            groupspath = (partitionpath.parent / descriptor["groups_file"]).resolve()
            assert groupspath == partitionpath.parent / f"batch-{index:06}/GROUPS.json"
            assert sha(groupspath) == descriptor["groups_sha256"]
            assert sha(groupspath.parent / "bindings.jsonl") == descriptor["bindings_sha256"]
            groups = read(groupspath)
            assert groups["group_count"] == len(groups["groups"]) == descriptor["count"]
            assert 0 < descriptor["count"] <= report["batch_size"]
            assert not (groupspath.parent / "PROPOSALS").exists()
            assert not (groupspath.parent / "EXACT-REPLAY.json").exists()
            count += descriptor["count"]
            descriptors.append((descriptor, groupspath))
    assert count == report["weak_graph_count"] and len(descriptors) == report["batch_count"]
    constantspath = HIGH.parent / f"evidence/core-reduction/constants/n{union['N']}.json"
    sources = (
        Path(__file__).resolve(), ROOT / "probe_collar_batches.py",
        HIGH / "replay_group_stage.py", HIGH / "exact_graph.py",
        ROOT / "audit_origin_collar_batches.py", ROOT / "batch_origin_collar.py",
        constantspath, partitionpath, descriptorpath, manifest, terminal, unionpath,
    )
    frozen = {str(path): sha(path) for path in sources}
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "schema": "one-shot-complete-origin-batch-jobs-v1",
        "N": union["N"], "B": union["B"], "weak_graph_count": count,
        "batch_count": len(descriptors), "workers": args.workers,
        "proposal_limit": 1, "numeric_weak_routing_is_not_a_cover_or_payment": True,
        "frozen_files": frozen, "catalog_sha256": sha(catalogpath),
        "parent_bindings_sha256": sha(bindingpath), "global_optimality_proved": False,
    })

    def run_batch(item):
        descriptor, groupspath = item
        stage = output / f"batch-{descriptor['batch']:06}"
        stage.mkdir()
        invoke(ROOT / "probe_collar_batches.py", [
            "--groups", groupspath, "--output", groupspath.parent / "PROPOSALS",
            "--limit", 1, "--route-weak-realizable"], stage, "PROPOSE", frozen)
        receiptpath = groupspath.parent / "PROPOSALS/SUMMARY.json"
        invoke(HIGH / "replay_group_stage.py", [
            "--groups", groupspath, "--receipt", receiptpath,
            "--output", groupspath.parent / "EXACT-REPLAY.json"], stage, "REPLAY", frozen)
        receipt, replay = read(receiptpath), read(groupspath.parent / "EXACT-REPLAY.json")
        assert receipt["requested_groups_complete"]
        assert replay["verified"] and replay["receipt_sha256"] == sha(receiptpath)
        assert replay["exact_groups_replayed"]+replay["pending_groups"] == descriptor["count"]
        assert replay["exact_groups_replayed"] == receipt["excluded_groups"]
        assert sha(groupspath) == descriptor["groups_sha256"]
        return {
            "batch": descriptor["batch"], "first": descriptor["first"], "count": descriptor["count"],
            "independently_replayed_strict_trees": replay["exact_groups_replayed"],
            "pending": replay["pending_groups"], "receipt_sha256": sha(receiptpath),
            "replay_sha256": sha(groupspath.parent / "EXACT-REPLAY.json"),
            "not_a_full_parent_payment_audit": True,
        }

    completed = strict = pending_count = 0
    started = time.monotonic()
    todo = iter(descriptors)
    try:
        with (output / "COMPLETED-BATCHES.jsonl").open("x", encoding="ascii") as ledger:
            with ThreadPoolExecutor(max_workers=args.workers) as executor:
                active = {executor.submit(run_batch, item) for item in
                          [next(todo) for _ in range(min(args.workers, len(descriptors)))]}
                while active:
                    done, active = wait(active, return_when=FIRST_COMPLETED)
                    results = [future.result() for future in done]
                    for result in results:
                        ledger.write(json.dumps(result, separators=(",", ":"))+"\n")
                        ledger.flush()
                        completed += 1
                        strict += result["independently_replayed_strict_trees"]
                        pending_count += result["pending"]
                        print("B", union["B"], "completed batches", completed, "/", len(descriptors),
                              "fresh replay trees", strict, "pending", pending_count,
                              "seconds", round(time.monotonic()-started, 2), flush=True)
                        item = next(todo, None)
                        if item is not None:
                            active.add(executor.submit(run_batch, item))
        assert completed == report["batch_count"] and strict+pending_count == count
        invoke(ROOT / "audit_origin_collar_batches.py", [
            "--manifest", manifest, "--terminal", terminal, "--union", unionpath,
            "--partition", partitionpath, "--output", output / "COMPLETE-PAYMENT-AUDIT"],
            output, "FULL-PARENT-AUDIT", frozen)
        acceptedpath = output / "COMPLETE-PAYMENT-AUDIT/VERIFIED.json"
        accepted = read(acceptedpath)
        assert accepted["verified"] and accepted["parent_weak_graphs"] == count
        assert accepted["strictly_excluded"] == strict and accepted["pending_weak_graphs"] == pending_count
        publish(output / "SUMMARY.json", {
            "scheduler_completed": True, "N": union["N"], "B": union["B"],
            "full_parent_acceptor_report_sha256": sha(acceptedpath),
            "strictly_excluded": strict, "pending_weak_graphs": pending_count,
            "all_residual_weak_lower_bounds_paid": pending_count == 0,
            "completed_batches_sha256": sha(output / "COMPLETED-BATCHES.jsonl"),
            "source_sha256": frozen[str(Path(__file__).resolve())],
            "global_optimality_proved": False,
        })
    except BaseException as error:
        publish(output / "FAILURE.json", {
            "scheduler_completed": False, "error_type": type(error).__name__,
            "error": str(error), "observed_completed_batches": completed,
            "no_full_parent_payment_claim": True, "outputs_preserved_no_retry_or_overwrite": True,
        })
        raise


if __name__ == "__main__":
    main()
