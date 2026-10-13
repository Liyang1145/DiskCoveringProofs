"""Full current small-order residual: ordinary jobs, fresh complete-parent adoption."""
from pathlib import Path
from collections import Counter
import argparse
import json
import os
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from small_order_collar_lower_pipeline import source_gate, rows
from small_order_filling_kernel import start_states
from replay_small_order_filling import replay

assert __debug__


def controls_gate(path):
    controls = read(path)
    assert controls["verified"] and controls["schema"] == "small-order-own-full-filling-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_small_order_filling.py")
    assert controls["kernel_sha256"] == sha(ROOT / "small_order_filling_kernel.py")
    assert controls["proposal_source_sha256"] == sha(ROOT / "propose_small_order_filling.py")
    assert controls["replay_source_sha256"] == sha(ROOT / "replay_small_order_filling.py")
    assert len(controls["complete_small_native_fiber_cases"]) == 8
    assert sum(row["pinched_collar_fibers"] for row in controls["complete_small_native_fiber_cases"]) >= 35
    assert controls["all_no_payment_full_sets_equal_to_complete_native_references"]
    assert controls["real_own_order_strict_family_separate_process_replayed"]
    assert controls["real_nonempty_branch_fiber_not_paid_without_force"]
    assert controls["proposal_limits_never_mistaken_for_completion"]
    assert len(controls["negative_controls_rejected"]) == 15
    for file, digest in controls["frozen_files"].items():
        assert sha(file) == digest


def parent_gate(stage, lower, check_old_trees=False):
    source = source_gate(stage)
    report = read(lower / "ACCEPTED/VERIFIED.json")
    assert report["verified"]
    assert report["schema"] == "small-order-complete-source-strict-weak-lower-audit-v1"
    assert report["source_sha256"] == sha(ROOT / "small_order_collar_lower_pipeline.py")
    assert (report["N"], report["B"], report["parent_weak_graphs"]) == (
        source["N"], source["B"], source["unique_necessary_weak_graphs"])
    assert report["source_acceptance_sha256"] == sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json")
    assert report["all_source_rows_disjointly_partitioned_and_actual_graph_maps_checked"]
    assert report["all_new_positive_trees_freshly_independently_math_replayed"]
    assert report["parent_weak_graphs"] == report["strictly_excluded"]+report["pending_weak_graphs"]
    for name, field in (
        ("PAYMENTS.jsonl", "payments_sha256"), ("PENDING.jsonl", "pending_sha256"),
        ("AUDITED-STAGES.jsonl", "audited_stages_sha256")):
        assert sha(lower / "ACCEPTED" / name) == report[field]
    assert sha(lower / "PARTITION.json") == report["partition_sha256"]
    pipeline, terminal, inputs = map(read, (
        lower / "PIPELINE-COMPLETED.json", lower / "AUDIT-TERMINAL.json",
        lower / "INPUT-BINDINGS.json"))
    assert pipeline["actual_all_proof_children_and_independent_audit_terminals_observed"]
    assert pipeline["report_sha256"] == sha(lower / "ACCEPTED/VERIFIED.json")
    assert pipeline["source_sha256"] == sha(ROOT / "small_order_collar_lower_pipeline.py")
    assert terminal["actual_exit_code"] == 0 and terminal["actual_child_terminal_observed"]
    assert Path(inputs["stage"]).resolve() == stage
    for file, digest in inputs["frozen_files"].items():
        assert sha(file) == digest
    if check_old_trees:
        checked, batches = 0, 0
        with (lower / "ACCEPTED/AUDITED-STAGES.jsonl").open(encoding="ascii") as stream:
            for line in stream:
                item = json.loads(line, object_pairs_hook=no_duplicate_keys)
                assert item["batch"] == batches
                directory = lower / f"batch-{batches:06}"
                for file, field in (
                    ("GROUPS.json", "groups_sha256"), ("bindings.jsonl", "bindings_sha256"),
                    ("PROPOSALS/SUMMARY.json", "receipt_sha256"),
                    ("PROPOSALS/EXACT-REPLAY.json", "exact_replay_sha256"),
                    ("TERMINAL.json", "proof_terminal_sha256"),
                    ("PROPOSALS/REPLAY-TERMINAL.json", "replay_terminal_sha256")):
                    assert sha(directory / file) == item[field]
                receipt = read(directory / "PROPOSALS/SUMMARY.json")
                assert receipt["source_sha256"] == sha(ROOT / "propose_isolated_small_order_groups.py")
                paid = 0
                for outcome in receipt["outcomes"]:
                    assert outcome["status"] in ("excluded", "pending")
                    if outcome["status"] == "excluded":
                        assert sha(directory / f"PROPOSALS/group-{outcome['group']:07}.json.gz") == outcome["tree_sha256"]
                        paid += 1
                assert paid == item["paid"]
                checked += paid
                batches += 1
                if batches % 50 == 0:
                    print("Old accepted weak-tree bytes rebound, not math replayed", checked, flush=True)
        assert checked == report["strictly_excluded"]
    return source, report


def pending_rows(lower, expected):
    count, previous = 0, -1
    with (lower / "ACCEPTED/PENDING.jsonl").open(encoding="ascii") as stream:
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert set(row) == {"parent_index", "batch", "group", "centers", "faces", "not_an_exclusion"}
            assert row["not_an_exclusion"]
            assert type(row["parent_index"]) is int and row["parent_index"] > previous
            previous, count = row["parent_index"], count+1
            yield row
    assert count == expected


def child(command, directory):
    with (directory / "REPLAY-STDOUT.log").open("xb") as stdout, \
            (directory / "REPLAY-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen(list(map(str, command)), stdout=stdout, stderr=stderr,
                                   cwd=str(ROOT),
                                   creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(directory / "REPLAY-TERMINAL.json", {
        "pid": process.pid, "actual_exit_code": code,
        "actual_child_terminal_observed": True, "command": list(map(str, command)),
        "source_sha256": sha(ROOT / "replay_small_order_filling.py")})
    assert code == 0, ("own-order family replay failed; preserve this original", directory)


def worker(jobpath, output):
    assert not output.exists()
    job = read(jobpath)
    assert job["schema"] == "small-order-actual-parent-residual-filling-job-v1"
    N, B = job["N"], job["B"]
    assert N in (23, 24)
    constantspath = ROOT.parent / f"evidence/core-reduction/constants/n{N}.json"
    assert job["constants_sha256"] == sha(constantspath)
    assert job["source_sha256"] == sha(Path(__file__))
    controls_gate(Path(job["controls_path"]))
    from propose_small_order_filling import propose
    constants = read(constantspath)
    output.mkdir()
    frozen = {str(path): sha(path) for path in (
        Path(__file__), jobpath, constantspath, Path(job["controls_path"]),
        ROOT / "small_order_filling_kernel.py", ROOT / "propose_small_order_filling.py",
        ROOT / "replay_small_order_filling.py")}
    outcomes = []
    for row in job["parents"]:
        pid = row["parent_index"]
        family = output / f"parent-{pid:07}"
        family.mkdir()
        collarpath = family / "INPUT-COLLAR.json"
        collar = {
            "N": N, "B": B, "centers": row["centers"], "faces": row["faces"],
            "actual_source_parent_index": pid,
            "actual_source_acceptance_sha256": job["source_acceptance_sha256"],
            "actual_current_lower_parent_report_sha256": job["lower_report_sha256"]}
        publish(collarpath, collar)
        frozen[str(collarpath)] = sha(collarpath)
        status = {"parent_index": pid, "centers": row["centers"], "faces": row["faces"]}
        try:
            start_states(N, B, row["centers"], row["faces"])
        except AssertionError as error:
            status.update(status="unhandled-source-topology", reason=str(error))
        else:
            payload = propose(collar, constants, job["topology_limit"], job["force_limit"])
            payload.update(
                source_collar_sha256=sha(collarpath), constants_sha256=sha(constantspath),
                kernel_sha256=sha(ROOT / "small_order_filling_kernel.py"),
                source_sha256=sha(ROOT / "propose_small_order_filling.py"),
                whole_family_payment_requires_independent_replay=True)
            proofpath, exactpath = family / "PROPOSAL.json", family / "EXACT.json"
            publish(proofpath, payload)
            child([sys.executable, "-u", ROOT / "replay_small_order_filling.py",
                   "--collar", collarpath, "--proposal", proofpath, "--output", exactpath], family)
            accepted = read(exactpath)
            assert accepted["verified"]
            status.update(
                status=("strict-complete-family" if accepted["whole_completion_family_strictly_closed"]
                        else "pending-complete-family"),
                pending_complete_leaves=accepted["pending_complete_leaves"],
                unsearched_frontier_nodes=accepted["unsearched_frontier_nodes"],
                proof_sha256=sha(proofpath), exact_sha256=sha(exactpath))
            for path in (proofpath, exactpath, family / "REPLAY-TERMINAL.json"):
                frozen[str(path)] = sha(path)
            for file, digest in accepted["frozen_files"].items():
                assert file not in frozen or frozen[file] == digest
                frozen[file] = digest
        outcomes.append(status)
    for file, digest in frozen.items():
        assert sha(file) == digest
    publish(output / "SUMMARY.json", {
        "schema": "small-order-complete-parent-filling-worker-v1",
        "N": N, "B": B, "job": job["job"], "first": job["first"],
        "count": len(job["parents"]), "outcomes": outcomes,
        "all_actual_child_terminals_observed": True, "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})


def partition(stage, lower, controls, work, source, base, batch_size, topology_limit, force_limit):
    selected = iter(pending_rows(lower, base["pending_weak_graphs"]))
    current, block, ordinal, first = next(selected, None), [], 0, 0
    N, B = source["N"], source["B"]
    with (work / "JOBS.jsonl").open("x", encoding="ascii") as descriptors:
        def flush():
            nonlocal ordinal, first
            if not block:
                return
            jobpath = work / f"job-{ordinal:06}.json"
            publish(jobpath, {
                "schema": "small-order-actual-parent-residual-filling-job-v1",
                "N": N, "B": B, "job": ordinal, "first": first,
                "parents": list(block), "controls_path": str(controls),
                "source_acceptance_sha256": sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json"),
                "lower_report_sha256": sha(lower / "ACCEPTED/VERIFIED.json"),
                "constants_sha256": sha(ROOT.parent / f"evidence/core-reduction/constants/n{N}.json"),
                "topology_limit": topology_limit, "force_limit": force_limit,
                "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})
            descriptors.write(json.dumps({
                "job": ordinal, "first": first, "count": len(block),
                "job_file": jobpath.name, "job_sha256": sha(jobpath)},
                separators=(",", ":"))+"\n")
            first += len(block)
            ordinal += 1
            block.clear()
        for original in rows(stage, source):
            if current is None or original["id"] < current["parent_index"]:
                continue
            assert original["id"] == current["parent_index"]
            assert (original["centers"], original["faces"]) == (current["centers"], current["faces"])
            block.append(current)
            if len(block) == batch_size:
                flush()
            current = next(selected, None)
        assert current is None
        flush()
    assert first == base["pending_weak_graphs"]
    publish(work / "PARTITION.json", {
        "verified": True, "N": N, "B": B, "pending_parents": first, "jobs": ordinal,
        "all_actual_pending_source_rows_exactly_compared_and_partitioned": True,
        "job_descriptors_sha256": sha(work / "JOBS.jsonl"),
        "lower_report_sha256": sha(lower / "ACCEPTED/VERIFIED.json"),
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})


def audit(stage, lower, work, controls, output):
    assert not output.exists()
    controls_gate(controls)
    source, base = parent_gate(stage, lower, True)
    partition_report = read(work / "PARTITION.json")
    assert partition_report["verified"]
    assert partition_report["source_sha256"] == sha(Path(__file__))
    assert partition_report["lower_report_sha256"] == sha(lower / "ACCEPTED/VERIFIED.json")
    assert partition_report["pending_parents"] == base["pending_weak_graphs"]
    assert partition_report["job_descriptors_sha256"] == sha(work / "JOBS.jsonl")
    output.mkdir()
    expected = iter(pending_rows(lower, base["pending_weak_graphs"]))
    count = paid = jobs = 0
    with (work / "JOBS.jsonl").open(encoding="ascii") as descriptors, \
            (work / "COMPLETED-JOBS.jsonl").open(encoding="ascii") as finished, \
            (output / "ADDITIONAL-PAYMENTS.jsonl").open("x", encoding="ascii") as payments, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as pending, \
            (output / "AUDITED-JOBS.jsonl").open("x", encoding="ascii") as audited:
        for line in descriptors:
            descriptor = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert descriptor["job"] == jobs and descriptor["first"] == count
            jobpath, directory = work / descriptor["job_file"], work / f"batch-{jobs:06}"
            assert jobpath == work / f"job-{jobs:06}.json" and sha(jobpath) == descriptor["job_sha256"]
            job, summary, terminal = map(read, (
                jobpath, directory / "SUMMARY.json", directory / "TERMINAL.json"))
            completed = json.loads(next(finished), object_pairs_hook=no_duplicate_keys)
            assert completed["job"] == jobs and completed["worker_report_sha256"] == sha(directory / "SUMMARY.json")
            assert terminal["actual_exit_code"] == 0 and terminal["actual_child_terminal_observed"]
            assert summary["source_sha256"] == sha(Path(__file__))
            assert summary["schema"] == "small-order-complete-parent-filling-worker-v1"
            assert (summary["N"], summary["B"], summary["job"], summary["first"]) == (
                source["N"], source["B"], jobs, count)
            assert len(summary["outcomes"]) == len(job["parents"]) == descriptor["count"] == summary["count"]
            for given, outcome in zip(job["parents"], summary["outcomes"], strict=True):
                original = next(expected)
                assert given == original
                assert (outcome["parent_index"], outcome["centers"], outcome["faces"]) == (
                    original["parent_index"], original["centers"], original["faces"])
                family = directory / f"parent-{original['parent_index']:07}"
                collarpath = family / "INPUT-COLLAR.json"
                collar = read(collarpath)
                assert (collar["N"], collar["B"], collar["centers"], collar["faces"]) == (
                    source["N"], source["B"], original["centers"], original["faces"])
                assert collar["actual_source_parent_index"] == original["parent_index"]
                assert collar["actual_source_acceptance_sha256"] == sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json")
                assert collar["actual_current_lower_parent_report_sha256"] == sha(lower / "ACCEPTED/VERIFIED.json")
                assert outcome["status"] in (
                    "unhandled-source-topology", "pending-complete-family", "strict-complete-family")
                if outcome["status"] == "unhandled-source-topology":
                    try:
                        start_states(source["N"], source["B"], original["centers"], original["faces"])
                    except AssertionError:
                        pass
                    else:
                        raise AssertionError("incorrect unhandled worker classification")
                else:
                    proofpath, exactpath = family / "PROPOSAL.json", family / "EXACT.json"
                    assert sha(proofpath) == outcome["proof_sha256"] and sha(exactpath) == outcome["exact_sha256"]
                    family_terminal = read(family / "REPLAY-TERMINAL.json")
                    assert family_terminal["actual_exit_code"] == 0 and family_terminal["actual_child_terminal_observed"]
                    assert family_terminal["source_sha256"] == sha(ROOT / "replay_small_order_filling.py")
                    fresh, old = replay(collarpath, proofpath), read(exactpath)
                    assert fresh == old
                    assert fresh["whole_completion_family_strictly_closed"] == (
                        outcome["status"] == "strict-complete-family")
                if outcome["status"] == "strict-complete-family":
                    payments.write(json.dumps({
                        "parent_index": original["parent_index"], "job": jobs,
                        "proof_sha256": outcome["proof_sha256"], "exact_sha256": outcome["exact_sha256"],
                        "not_a_geometric_weak_graph_strict_exclusion": True}, separators=(",", ":"))+"\n")
                    paid += 1
                else:
                    pending.write(json.dumps({**original, "job": jobs, "status": outcome["status"]},
                                             separators=(",", ":"))+"\n")
                count += 1
            for file, digest in summary["frozen_files"].items():
                assert sha(file) == digest
            audited.write(json.dumps({
                "job": jobs, "worker_report_sha256": sha(directory / "SUMMARY.json"),
                "terminal_sha256": sha(directory / "TERMINAL.json"), "job_sha256": sha(jobpath)},
                separators=(",", ":"))+"\n")
            jobs += 1
            if jobs % 10 == 0:
                print("Own-order complete-parent new families freshly replayed", count,
                      "/", base["pending_weak_graphs"], "strict whole", paid, flush=True)
        assert not finished.read().strip()
    assert next(expected, None) is None
    assert count == base["pending_weak_graphs"] and jobs == partition_report["jobs"]
    assert parent_gate(stage, lower)[0] == source
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "small-order-full-parent-weak-and-complete-filling-disjoint-adoption-v1",
        "N": source["N"], "B": source["B"], "parent_weak_graphs": base["parent_weak_graphs"],
        "old_strict_weak_graphs": base["strictly_excluded"],
        "new_strict_complete_families": paid, "pending_families": count-paid,
        "full_parent_partition_complete": base["parent_weak_graphs"] == base["strictly_excluded"]+paid+(count-paid),
        "all_actual_current_residual_source_graphs_and_indices_compared": True,
        "all_new_completion_family_branches_and_math_freshly_independently_replayed": True,
        "all_old_strict_weak_tree_bytes_rebound_old_math_honestly_reused": True,
        "source_acceptance_sha256": sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json"),
        "old_weak_lower_report_sha256": sha(lower / "ACCEPTED/VERIFIED.json"),
        "partition_sha256": sha(work / "PARTITION.json"),
        "additional_payments_sha256": sha(output / "ADDITIONAL-PAYMENTS.jsonl"),
        "pending_sha256": sha(output / "PENDING.jsonl"), "audited_jobs_sha256": sha(output / "AUDITED-JOBS.jsonl"),
        "source_sha256": sha(Path(__file__)), "complete_source_lower_family_paid": count == paid,
        "arbitrary_cover_transport_other_families_and_same_root_global_synthesis_still_required": True,
        "global_optimality_proved": False})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--worker", type=Path)
    ap.add_argument("--audit", action="store_true")
    for name in ("stage", "lower", "controls", "output", "work"):
        ap.add_argument("--"+name, type=Path, required=name == "output")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--batch-size", type=int, default=64)
    ap.add_argument("--topology-limit", type=int, default=10000)
    ap.add_argument("--force-limit", type=int, default=31)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    if args.worker:
        worker(args.worker.resolve(), output)
        return
    stage, lower, controls = (getattr(args, key).resolve() for key in ("stage", "lower", "controls"))
    assert all(path.is_relative_to(ROOT) for path in (stage, lower, controls))
    if args.audit:
        audit(stage, lower, args.work.resolve(), controls, output)
        return
    assert 1 <= args.workers <= 4 and 1 <= args.batch_size <= 256
    assert 1 <= args.topology_limit <= 100000 and 1 <= args.force_limit <= 10001
    assert shutil.disk_usage(ROOT).free >= 12*1024**3
    controls_gate(controls)
    source, base = parent_gate(stage, lower, True)
    output.mkdir()
    frozen = {str(path): sha(path) for path in (
        Path(__file__), controls, stage / "ACCEPTED/SOURCE-ACCEPTED.json",
        lower / "ACCEPTED/VERIFIED.json", ROOT / "small_order_filling_kernel.py",
        ROOT / "propose_small_order_filling.py", ROOT / "replay_small_order_filling.py")}
    publish(output / "INPUT-BINDINGS.json", {
        "N": source["N"], "B": source["B"], "stage": str(stage), "lower": str(lower),
        "controls": str(controls), "workers": args.workers, "batch_size": args.batch_size,
        "topology_limit": args.topology_limit, "force_limit": args.force_limit,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})
    partition(stage, lower, controls, output, source, base,
              args.batch_size, args.topology_limit, args.force_limit)
    jobs = [json.loads(line) for line in (output / "JOBS.jsonl").read_text().splitlines()]
    active, launched, done, totals, completed = [], 0, 0, Counter(), {}
    with (output / "COMPLETED-JOBS.jsonl").open("x", encoding="ascii") as ledger:
        while done < len(jobs):
            while launched < len(jobs) and len(active) < args.workers:
                assert shutil.disk_usage(ROOT).free >= 9*1024**3, "reserved-space guard; not completion"
                directory = output / f"batch-{launched:06}"
                stdout = (output / f"batch-{launched:06}-STDOUT.log").open("xb")
                stderr = (output / f"batch-{launched:06}-STDERR.log").open("xb")
                process = subprocess.Popen(list(map(str, [
                    sys.executable, "-u", Path(__file__), "--worker",
                    output / jobs[launched]["job_file"], "--output", directory])),
                    cwd=str(ROOT), stdout=stdout, stderr=stderr,
                    env=dict(os.environ, OPENBLAS_NUM_THREADS="1",
                             OMP_NUM_THREADS="1", MKL_NUM_THREADS="1"),
                    creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
                active.append((launched, process, directory, stdout, stderr))
                launched += 1
            for item in active[:]:
                ordinal, process, directory, stdout, stderr = item
                code = process.poll()
                if code is None:
                    continue
                stdout.close()
                stderr.close()
                publish(directory / "TERMINAL.json", {
                    "pid": process.pid, "actual_exit_code": code,
                    "actual_child_terminal_observed": True, "source_sha256": sha(Path(__file__))})
                assert code == 0, ("original own-order worker failed; do not restart blindly", directory)
                summary = read(directory / "SUMMARY.json")
                totals.update(row["status"] for row in summary["outcomes"])
                completed[ordinal] = sha(directory / "SUMMARY.json")
                active.remove(item)
                done += 1
                print("Own-order whole residual filling proposals", done, "/", len(jobs),
                      dict(totals), flush=True)
            time.sleep(0.2)
        for ordinal in range(len(jobs)):
            ledger.write(json.dumps({"job": ordinal, "worker_report_sha256": completed[ordinal]},
                                    separators=(",", ":"))+"\n")
    for file, digest in frozen.items():
        assert sha(file) == digest
    with (output / "AUDIT-STDOUT.log").open("xb") as stdout, \
            (output / "AUDIT-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen(list(map(str, [
            sys.executable, "-u", Path(__file__), "--audit", "--stage", stage,
            "--lower", lower, "--controls", controls, "--work", output,
            "--output", output / "ACCEPTED"])), cwd=str(ROOT), stdout=stdout, stderr=stderr,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / "AUDIT-TERMINAL.json", {
        "pid": process.pid, "actual_exit_code": code, "actual_child_terminal_observed": True})
    assert code == 0
    for file, digest in frozen.items():
        assert sha(file) == digest
    publish(output / "PIPELINE-COMPLETED.json", {
        "actual_all_original_workers_and_independent_parent_audit_terminals_observed": True,
        "report_sha256": sha(output / "ACCEPTED/VERIFIED.json"),
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})


if __name__ == "__main__":
    main()
