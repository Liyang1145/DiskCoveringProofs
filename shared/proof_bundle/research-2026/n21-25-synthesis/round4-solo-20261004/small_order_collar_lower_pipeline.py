"""Own-order complete-source partition, ordinary proof jobs, separate exact audit."""
from pathlib import Path
from fractions import Fraction as F
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
from group_catalog import canonical, validate
from audit_small_order_origin_union import inputs_gate
from audit_origin_collar_batches import verify_tree
from batch_origin_collar import identity

assert __debug__


def source_record_gate(record, stage):
    assert record["verified"]
    assert record["schema"] == "small-order-complete-necessary-origin-outer-family-source-and-union-v1"
    assert record["N"] in (23, 24)
    assert record["complete_recorded_necessary_outer_family"]
    assert record["actual_native_successful_terminal_and_exact_source_inputs_rechecked"]
    assert record["all_declared_sorted_slabs_and_full_union_independently_verified"]
    assert record["weak_graph_rows_not_full_type_lower_bound_payments"]
    assert record["source_sha256"] == sha(ROOT / "audit_small_order_origin_union.py")
    assert not record["global_optimality_proved"]
    assert type(record["unique_necessary_weak_graphs"]) is int
    assert record["unique_necessary_weak_graphs"] >= 0
    files = record["frozen_files"]
    for name in ("VERIFIED.json", "CATALOG.jsonl", "bindings.jsonl"):
        path = stage / "ACCEPTED" / name
        assert str(path) in files and sha(path) == files[str(path)]
    assert record["catalog_sha256"] == sha(stage / "ACCEPTED/CATALOG.jsonl")
    assert record["union_report_sha256"] == sha(stage / "ACCEPTED/VERIFIED.json")


def source_gate(stage):
    stage = Path(stage).resolve()
    assert stage.is_relative_to(ROOT)
    recordpath = stage / "ACCEPTED/SOURCE-ACCEPTED.json"
    record = read(recordpath)
    source_record_gate(record, stage)
    _, inputs, _ = inputs_gate(
        stage, ROOT / "small-order-origin-source-controls-v2/VERIFIED.json",
        ROOT / "small-order-own-caps-v1/VERIFIED.json")
    assert (record["N"], record["B"]) == (inputs["N"], inputs["B"])
    for path, digest in record["frozen_files"].items():
        assert sha(path) == digest
    pipeline = read(stage / "PIPELINE-COMPLETED.json")
    assert pipeline["actual_native_and_union_terminals_observed"]
    assert pipeline["source_acceptance_sha256"] == sha(recordpath)
    assert pipeline["source_sha256"] == sha(ROOT / "run_small_order_origin_search.py")
    union = read(stage / "ACCEPTED/VERIFIED.json")
    assert (union["N"], union["B"], union["unique_necessary_weak_graphs"]) == (
        record["N"], record["B"], record["unique_necessary_weak_graphs"])
    return record


def row_gate(row, N, B, index, check_canonical=False):
    assert set(row) == {"id", "centers", "faces", "members"}
    assert type(row["id"]) is int and row["id"] == index
    assert type(row["members"]) is int and row["members"] == 1
    centers, faces = row["centers"], row["faces"]
    assert type(centers) is int and B <= centers < N
    assert faces and faces == sorted(set(faces))
    assert all(type(mask) is int and 0 < mask < 1 << centers
               and mask.bit_count() == 3 and mask & ((1 << B)-1) for mask in faces)
    used = 0
    for mask in faces:
        used |= mask
    assert used == (1 << centers)-1
    if check_canonical:
        code, mapping = canonical(centers, B, faces, 1)
        assert code == tuple(faces)
        validate(centers, B, faces, mapping, faces)


def rows(stage, record, check_canonical=False):
    N, B = record["N"], record["B"]
    previous, count = None, 0
    with (stage / "ACCEPTED/CATALOG.jsonl").open(encoding="ascii") as stream:
        header = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
        assert header == {
            "schema": "complete-necessary-small-order-collar-union-v1",
            "N": N, "B": B, "members_are_weak_graphs_not_full_types": True}
        for index, line in enumerate(stream):
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            row_gate(row, N, B, index, check_canonical)
            code = tuple(row["faces"])
            assert previous is None or previous < code
            previous, count = code, count+1
            yield row
    assert count == record["unique_necessary_weak_graphs"]


def make_groups(block, N, B, total, cataloghash, directory, batch):
    directory.mkdir()
    bindingpath = directory / "bindings.jsonl"
    with bindingpath.open("x", encoding="ascii") as stream:
        for local, row in enumerate(block):
            stream.write(json.dumps({
                "index": row["id"], "group": local,
                "map": identity(row["centers"], B)}, separators=(",", ":"))+"\n")
    publish(directory / "GROUPS.json", {
        "N": N, "B": B, "threshold": 1,
        "groups": [{"id": i, "centers": row["centers"], "faces": row["faces"], "members": 1}
                   for i, row in enumerate(block)],
        "group_count": len(block), "selected_types": len(block), "catalog_types": total,
        "catalog_sha256": cataloghash, "bindings_file": bindingpath.name,
        "bindings_sha256": sha(bindingpath), "verified_embeddings_during_generation": True,
        "full_selected_catalog_scanned": True,
        "selected_batch_only_not_whole_family": True,
        "parent_catalog_first_index": block[0]["id"], "batch_number": batch,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })


def partition(stage, output, record, batch_size):
    N, B, total = record["N"], record["B"], record["unique_necessary_weak_graphs"]
    block, count, batches = [], 0, 0
    descriptorpath = output / "BATCHES.jsonl"
    with descriptorpath.open("x", encoding="ascii") as descriptors, \
            (stage / "ACCEPTED/bindings.jsonl").open(encoding="ascii") as bindings:
        def flush():
            nonlocal batches
            if not block:
                return
            directory = output / f"batch-{batches:06}"
            make_groups(block, N, B, total, record["catalog_sha256"], directory, batches)
            descriptors.write(json.dumps({
                "batch": batches, "first": block[0]["id"], "count": len(block),
                "groups_sha256": sha(directory / "GROUPS.json"),
                "bindings_sha256": sha(directory / "bindings.jsonl")},
                separators=(",", ":"))+"\n")
            batches += 1
            block.clear()
        for row in rows(stage, record, True):
            binding = json.loads(next(bindings), object_pairs_hook=no_duplicate_keys)
            assert binding == {
                "index": count, "group": count, "map": identity(row["centers"], B)}
            block.append(row)
            count += 1
            if len(block) == batch_size:
                flush()
        flush()
        assert not bindings.read().strip()
    assert count == total
    publish(output / "PARTITION.json", {
        "verified": True, "schema": "small-order-complete-source-lower-partition-v1",
        "N": N, "B": B, "parent_rows": total, "batch_count": batches,
        "batch_size": batch_size, "descriptor_sha256": sha(descriptorpath),
        "source_acceptance_sha256": sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json"),
        "parent_catalog_sha256": record["catalog_sha256"],
        "all_parent_rows_and_identity_maps_checked": True,
        "partition_never_a_lower_bound_payment": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })


def audit(stage, work, output):
    record = source_gate(stage)
    assert not output.exists()
    N, B, total = record["N"], record["B"], record["unique_necessary_weak_graphs"]
    partition_report = read(work / "PARTITION.json")
    assert partition_report["verified"]
    assert partition_report["schema"] == "small-order-complete-source-lower-partition-v1"
    assert partition_report["source_sha256"] == sha(Path(__file__))
    assert (partition_report["N"], partition_report["B"], partition_report["parent_rows"]) == (N, B, total)
    assert partition_report["all_parent_rows_and_identity_maps_checked"]
    assert partition_report["source_acceptance_sha256"] == sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json")
    assert partition_report["parent_catalog_sha256"] == record["catalog_sha256"]
    assert partition_report["descriptor_sha256"] == sha(work / "BATCHES.jsonl")
    constants_path = ROOT.parent / f"evidence/core-reduction/constants/n{N}.json"
    constants, constantshash = read(constants_path), sha(constants_path)
    assert constants["verified"] and constants["N"] == N
    output.mkdir()
    count = paid = batches = 0
    minimum = None
    originals = iter(rows(stage, record))
    with (work / "BATCHES.jsonl").open(encoding="ascii") as descriptors, \
            (output / "PAYMENTS.jsonl").open("x", encoding="ascii") as payments, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as pending, \
            (output / "AUDITED-STAGES.jsonl").open("x", encoding="ascii") as stages:
        for line in descriptors:
            descriptor = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert descriptor["batch"] == batches and descriptor["first"] == count
            directory = work / f"batch-{batches:06}"
            groupspath, bindingpath = directory / "GROUPS.json", directory / "bindings.jsonl"
            assert sha(groupspath) == descriptor["groups_sha256"]
            assert sha(bindingpath) == descriptor["bindings_sha256"]
            data, receipt, replay, terminal = map(read, (
                groupspath, directory / "PROPOSALS/SUMMARY.json",
                directory / "PROPOSALS/EXACT-REPLAY.json", directory / "TERMINAL.json"))
            assert terminal["actual_exit_code"] == 0 and terminal["actual_child_terminal_observed"]
            assert terminal["source_sha256"] == sha(ROOT / "propose_isolated_small_order_groups.py")
            child_terminal = read(directory / "PROPOSALS/REPLAY-TERMINAL.json")
            assert child_terminal["actual_exit_code"] == 0
            assert child_terminal["independent_process_terminal_observed"]
            assert child_terminal["source_sha256"] == sha(HIGH / "replay_group_stage.py")
            digest = sha(groupspath)
            assert receipt["groups_sha256"] == replay["groups_sha256"] == digest
            assert receipt["requested_groups_complete"] and replay["verified"]
            assert receipt["source_sha256"] == sha(ROOT / "propose_isolated_small_order_groups.py")
            assert replay["source_sha256"] == sha(HIGH / "replay_group_stage.py")
            assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
            assert replay["receipt_sha256"] == sha(directory / "PROPOSALS/SUMMARY.json")
            assert replay["bindings_sha256"] == sha(bindingpath)
            assert (data["N"], data["B"], data["catalog_types"]) == (N, B, total)
            assert (receipt["N"], receipt["B"]) == (replay["N"], replay["B"]) == (N, B)
            assert data["catalog_sha256"] == record["catalog_sha256"]
            assert data["source_sha256"] == sha(Path(__file__))
            assert data["parent_catalog_first_index"] == count and data["batch_number"] == batches
            assert data["selected_batch_only_not_whole_family"]
            assert len(data["groups"]) == data["group_count"] == descriptor["count"]
            assert data["selected_types"] == data["group_count"]
            outcomes = receipt["outcomes"]
            assert len(outcomes) == data["group_count"]
            assert [o["group"] for o in outcomes] == list(range(data["group_count"]))
            batch_paid = 0
            with bindingpath.open(encoding="ascii") as bindings:
                for local, (group, outcome) in enumerate(zip(data["groups"], outcomes, strict=True)):
                    parent = next(originals)
                    assert group == {"id": local, "centers": parent["centers"],
                                     "faces": parent["faces"], "members": 1}
                    assert parent["id"] == count
                    assert json.loads(next(bindings), object_pairs_hook=no_duplicate_keys) == {
                        "index": count, "group": local, "map": identity(group["centers"], B)}
                    assert outcome["status"] in ("excluded", "pending")
                    if outcome["status"] == "pending":
                        pending.write(json.dumps({
                            "parent_index": count, "batch": batches, "group": local,
                            "centers": parent["centers"], "faces": parent["faces"],
                            "not_an_exclusion": True}, separators=(",", ":"))+"\n")
                    else:
                        result, margin = verify_tree(
                            N, B, group, outcome, directory / "PROPOSALS/SUMMARY.json",
                            digest, constants, constantshash)
                        minimum = margin if minimum is None else min(minimum, margin)
                        payments.write(json.dumps({
                            "parent_index": count, "tree_sha256": outcome["tree_sha256"],
                            "minimum_force_margin": str(margin)}, separators=(",", ":"))+"\n")
                        batch_paid += 1
                        paid += 1
                    count += 1
                assert not bindings.read().strip()
            assert batch_paid == receipt["excluded_groups"] == replay["exact_groups_replayed"]
            assert batch_paid == receipt["catalog_members_excluded"] == replay["associated_member_count"]
            assert data["group_count"]-batch_paid == receipt["pending_groups"] == replay["pending_groups"]
            for path, digest in receipt["frozen_files"].items():
                assert sha(path) == digest
            stages.write(json.dumps({
                "batch": batches, "groups_sha256": sha(groupspath),
                "bindings_sha256": sha(bindingpath),
                "receipt_sha256": sha(directory / "PROPOSALS/SUMMARY.json"),
                "exact_replay_sha256": sha(directory / "PROPOSALS/EXACT-REPLAY.json"),
                "proof_terminal_sha256": sha(directory / "TERMINAL.json"),
                "replay_terminal_sha256": sha(directory / "PROPOSALS/REPLAY-TERMINAL.json"),
                "paid": batch_paid, "pending": data["group_count"]-batch_paid},
                separators=(",", ":"))+"\n")
            batches += 1
            if batches % 10 == 0:
                print("Small-order source lower audit", count, "/", total, "strict", paid, flush=True)
    assert next(originals, None) is None
    assert count == total and batches == partition_report["batch_count"]
    assert source_gate(stage) == record
    assert sha(constants_path) == constantshash
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "small-order-complete-source-strict-weak-lower-audit-v1",
        "N": N, "B": B, "parent_weak_graphs": total, "strictly_excluded": paid,
        "pending_weak_graphs": total-paid,
        "all_source_rows_disjointly_partitioned_and_actual_graph_maps_checked": True,
        "all_new_positive_trees_freshly_independently_math_replayed": True,
        "source_acceptance_sha256": sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json"),
        "partition_sha256": sha(work / "PARTITION.json"),
        "payments_sha256": sha(output / "PAYMENTS.jsonl"),
        "pending_sha256": sha(output / "PENDING.jsonl"),
        "audited_stages_sha256": sha(output / "AUDITED-STAGES.jsonl"),
        "minimum_force_margin": None if minimum is None else str(minimum),
        "constants_sha256": constantshash, "source_sha256": sha(Path(__file__)),
        "all_weak_lower_bounds_paid": paid == total,
        "remaining_completion_cover_and_other_families_still_required": True,
        "global_optimality_proved": False,
    })


def run(stage, core, controls, output, batch_size, workers, limit):
    assert not output.exists() and 1 <= workers <= 4 and 1 <= batch_size <= 1024
    assert 1 <= limit <= 10001
    record = source_gate(stage)
    control = read(controls)
    assert control["verified"] and control["source_sha256"] == sha(Path(__file__))
    assert control["control_source_sha256"] == sha(ROOT / "test_small_order_collar_lower_pipeline.py")
    assert len(control["negative_controls_rejected"]) == 21
    assert control["real_source_record_and_row_refusals_passed"]
    assert control["real_own_order_positive_tree_replayed"]
    assert read(core)["N"] == record["N"]
    frozen = {str(path): sha(path) for path in (
        Path(__file__), controls, core, ROOT / "propose_isolated_small_order_groups.py",
        ROOT / "probe_collar_batches.py", ROOT / "audit_origin_collar_batches.py",
        HIGH / "exact_graph.py", HIGH / "candidate_domain.py", HIGH / "replay_group_stage.py")}
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "stage": str(stage), "core": str(core), "workers": workers,
        "batch_size": batch_size, "force_limit": limit, "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})
    partition(stage, output, record, batch_size)
    descriptors = [json.loads(line) for line in (output / "BATCHES.jsonl").read_text().splitlines()]
    active, launched, done, strict, pending = [], 0, 0, 0, 0
    proposer = ROOT / "propose_isolated_small_order_groups.py"
    while done < len(descriptors):
        while launched < len(descriptors) and len(active) < workers:
            descriptor = descriptors[launched]
            directory = output / f"batch-{launched:06}"
            command = list(map(str, [
                sys.executable, "-u", proposer, "--groups", directory / "GROUPS.json",
                "--core", core, "--limit", limit, "--output", directory / "PROPOSALS"]))
            stdout = (directory / "STDOUT.log").open("xb")
            stderr = (directory / "STDERR.log").open("xb")
            process = subprocess.Popen(command, stdout=stdout, stderr=stderr, cwd=str(ROOT),
                                       env=dict(os.environ, OPENBLAS_NUM_THREADS="1",
                                                OMP_NUM_THREADS="1", MKL_NUM_THREADS="1"),
                                       creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
            publish(directory / "LAUNCH.json", {"pid": process.pid, "command": command})
            active.append((process, directory, stdout, stderr))
            launched += 1
        for job in active[:]:
            process, directory, stdout, stderr = job
            code = process.poll()
            if code is None:
                continue
            stdout.close()
            stderr.close()
            publish(directory / "TERMINAL.json", {
                "pid": process.pid, "actual_exit_code": code,
                "actual_child_terminal_observed": True, "source_sha256": sha(proposer)})
            assert code == 0, f"proof job failed: {directory}; other originals must not be restarted"
            receipt = read(directory / "PROPOSALS/SUMMARY.json")
            strict += receipt["excluded_groups"]
            pending += receipt["pending_groups"]
            active.remove(job)
            done += 1
            print("Small-order complete weak lower proposals", done, "/", len(descriptors),
                  "batches; strict", strict, "pending", pending, flush=True)
        time.sleep(0.2)
    for path, digest in frozen.items():
        assert sha(path) == digest
    with (output / "AUDIT-STDOUT.log").open("xb") as stdout, \
            (output / "AUDIT-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen(list(map(str, [
            sys.executable, "-u", Path(__file__), "--audit", "--stage", stage,
            "--work", output, "--output", output / "ACCEPTED"])),
            cwd=str(ROOT), stdout=stdout, stderr=stderr,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / "AUDIT-TERMINAL.json", {
        "pid": process.pid, "actual_exit_code": code, "actual_child_terminal_observed": True})
    assert code == 0
    for path, digest in frozen.items():
        assert sha(path) == digest
    publish(output / "PIPELINE-COMPLETED.json", {
        "actual_all_proof_children_and_independent_audit_terminals_observed": True,
        "report_sha256": sha(output / "ACCEPTED/VERIFIED.json"),
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})
    print("Small-order entire weak-source strict layer accepted; pending completions still owed", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--audit", action="store_true")
    for name in ("stage", "output", "core", "controls", "work"):
        ap.add_argument("--"+name, type=Path, required=name in ("stage", "output"))
    ap.add_argument("--batch-size", type=int, default=128)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--limit", type=int, default=1)
    args = ap.parse_args()
    stage, output = args.stage.resolve(), args.output.resolve()
    assert all(path.is_relative_to(ROOT) for path in (stage, output))
    if args.audit:
        assert args.work is not None
        audit(stage, args.work.resolve(), output)
    else:
        assert args.core is not None and args.controls is not None
        run(stage, args.core.resolve(), args.controls.resolve(), output,
            args.batch_size, args.workers, args.limit)


if __name__ == "__main__":
    main()
