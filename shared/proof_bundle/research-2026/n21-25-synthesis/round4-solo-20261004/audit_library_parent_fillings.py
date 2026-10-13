"""Full-parent incremental filling acceptance from a verified library parent.

The immutable accepted weak/library parent is a prerequisite, with all its
bound bytes checked again. Every NEW filling tree is mathematically replayed,
and every parent row is disjointly repartitioned. Old trees are not claimed to
be mathematically replayed in this incremental layer.
"""
from pathlib import Path
from collections import Counter
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish, unchanged
from library_parent_pending_worklist import select
from batch_origin_collar import parent_gate, catalog_rows
from audit_complete_origin_finer_supplement import valid_payment_partition, full_filling_source
from audit_complete_origin_fillings import match_family_source
from linked_general_collar_kernel import replay

assert __debug__


def check_job_partition(entries, jobs):
    positions = [entry["snapshot_position"] for entry in entries]
    assert positions == sorted(set(positions)) and positions
    assert all(type(pos) is int and pos >= 0 for pos in positions)
    flattened, offset = [], 0
    for ordinal, job in enumerate(jobs):
        assert type(job["job"]) is int and job["job"] == ordinal
        assert type(job["first"]) is int and type(job["count"]) is int
        assert type(job["selected_offset"]) is int
        assert 1 <= job["count"] <= 1024 and job["selected_offset"] == offset
        flattened.extend(range(job["first"], job["first"]+job["count"]))
        offset += job["count"]
    assert flattened == positions and offset == len(entries)


def main():
    ap = argparse.ArgumentParser()
    for name in ("snapshot", "base", "stage", "controls", "job-controls", "audit-controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    snapshotpath, basepath, stage, controls_path, jobcontrols_path, auditcontrols_path, output = (
        getattr(args, name.replace("-", "_")).resolve() for name in (
            "snapshot", "base", "stage", "controls", "job-controls", "audit-controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (
        snapshotpath, basepath, stage, controls_path, jobcontrols_path, auditcontrols_path, output))
    assert not output.exists()
    controls, jobcontrols, auditcontrols = map(read, (controls_path, jobcontrols_path, auditcontrols_path))
    assert controls["verified"] and controls["schema"] == "linked-general-collar-filling-controls-v1"
    assert controls["kernel_sha256"] == sha(ROOT / "linked_general_collar_kernel.py")
    assert controls["known_attaining_candidate_not_strictly_paid"]
    unchanged(controls["files_relative_to_workspace"])
    assert jobcontrols["verified"] and jobcontrols["schema"] == "original-snapshot-gapped-job-partition-controls-v1"
    assert jobcontrols["source_sha256"] == sha(ROOT / "test_library_parent_gapped_jobs.py")
    assert jobcontrols["selection_source_sha256"] == sha(ROOT / "library_parent_pending_worklist.py")
    assert auditcontrols["verified"] and auditcontrols["schema"] == "library-parent-filling-job-audit-controls-v1"
    assert auditcontrols["source_sha256"] == sha(ROOT / "test_library_parent_filling_audit.py")
    assert auditcontrols["audit_source_sha256"] == sha(Path(__file__))
    sourcecontrols_path = ROOT / "complete-origin-filling-parent-source-controls-20261005-v1/VERIFIED.json"
    sourcecontrols = read(sourcecontrols_path)
    assert sourcecontrols["verified"] and sourcecontrols["merge_source_sha256"] == sha(ROOT / "audit_complete_origin_fillings.py")
    snapshot, base, expected = select(snapshotpath, basepath)
    worklist, jobs_report, inputs = map(read, (
        stage / "WORKLIST.json", stage / "SUMMARY.json", stage / "INPUT-BINDINGS.json"))
    assert worklist["schema"] == "accepted-library-parent-original-root-snapshot-residual-worklist-v1"
    assert worklist["source_sha256"] == jobs_report["source_sha256"] == sha(ROOT / "pay_library_parent_pending.py")
    assert worklist["entries"] == expected
    assert worklist["source_root_snapshot_sha256"] == inputs["snapshot_sha256"] == sha(snapshotpath)
    assert worklist["accepted_library_parent_sha256"] == inputs["base_report_sha256"] == sha(basepath / "VERIFIED.json")
    assert worklist["original_root_snapshot_unchanged_and_not_relabelled"]
    assert worklist["all_library_paid_source_positions_skipped"]
    assert inputs["worklist_sha256"] == jobs_report["worklist_sha256"] == sha(stage / "WORKLIST.json")
    assert jobs_report["scheduler_completed"] and jobs_report["schema"] == "library-parent-gapped-original-snapshot-filling-jobs-v1"
    assert jobs_report["selected_graphs"] == inputs["selected_original_pending_graphs"] == len(expected)
    assert jobs_report["completed_batches_sha256"] == sha(stage / "COMPLETED-BATCHES.jsonl")
    check_job_partition(expected, worklist["jobs"])
    assert len(worklist["jobs"]) == jobs_report["job_count"]
    N, B = snapshot["N"], snapshot["B"]
    assert (worklist["N"], worklist["B"]) == (jobs_report["N"], jobs_report["B"]) == (N, B)
    files = dict(base["frozen_files"])
    for path, digest in worklist["frozen_files"].items():
        assert sha(path) == digest
        files[path] = digest
    descriptors = {}
    with (stage / "COMPLETED-BATCHES.jsonl").open(encoding="ascii") as stream:
        for line in stream:
            item = json.loads(line, object_pairs_hook=no_duplicate_keys)
            ordinal = item["job"]
            assert type(ordinal) is int and ordinal not in descriptors
            descriptors[ordinal] = item
    assert set(descriptors) == set(range(len(worklist["jobs"])))
    constantspath = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants, digest, constantshash = read(constantspath), sha(snapshotpath), sha(constantspath)
    outcomes, newpaid, worker_counts = {}, {}, Counter()
    for job in worklist["jobs"]:
        descriptor = descriptors[job["job"]]
        assert all(descriptor[key] == value for key, value in job.items())
        directory = stage / f"batch-{job['job']:06}"
        reportpath = directory / "SUMMARY.json"
        assert sha(reportpath) == descriptor["worker_report_sha256"]
        worker = read(reportpath)
        assert worker["source_sha256"] == sha(ROOT / "pay_complete_origin_pending.py")
        assert worker["schema"] == "complete-parent-pending-filling-worker-v1"
        assert worker["snapshot_sha256"] == digest
        assert (worker["first"], worker["count"]) == (job["first"], job["count"])
        selected = expected[job["selected_offset"]:job["selected_offset"]+job["count"]]
        assert len(selected) == len(worker["outcomes"])
        assert Counter(row["status"] for row in worker["outcomes"]) == descriptor["counts"]
        for path, oldhash in worker["frozen_files"].items():
            assert sha(path) == oldhash
            files[path] = oldhash
        for row, status in zip(selected, worker["outcomes"], strict=True):
            pid = row["parent_index"]
            assert pid not in outcomes
            assert (status["parent_index"], status["centers"], status["faces"]) == (
                pid, row["centers"], row["faces"])
            assert status["status"] in ("pending", "strict-complete-filling-family")
            outcomes[pid] = status
            worker_counts[status["status"]] += 1
            if status["status"] == "pending":
                continue
            family = directory / f"parent-{pid:07}"
            collarpath = family / "INPUT-COLLAR.json"
            proofpath = (directory / status["proof_relative_to_stage"]).resolve()
            exactpath = (directory / status["exact_relative_to_stage"]).resolve()
            assert proofpath.is_relative_to(family) and exactpath.is_relative_to(family)
            assert sha(proofpath) == status["proof_sha256"] and sha(exactpath) == status["exact_sha256"]
            collar, payload, recorded = map(read, (collarpath, proofpath, exactpath))
            match_family_source(status, collar, payload, N, B, digest)
            assert payload["source_collar_sha256"] == sha(collarpath)
            full_filling_source(row, payload, recorded, N, B, constantshash)
            unchanged(recorded["files_relative_to_workspace"])
            result = replay(proofpath, constants)
            assert result["all_full_simple_disk_completions_strictly_paid"]
            assert all(recorded[key] == value for key, value in result.items())
            newpaid[pid] = {
                "parent_index": pid, "status": "strict-complete-filling-family",
                "proof_sha256": status["proof_sha256"], "exact_sha256": status["exact_sha256"],
                "not_a_standalone_geometric_weak_graph_exclusion": True,
            }
            for path in (collarpath, proofpath, exactpath):
                files[str(path)] = sha(path)
            if len(newpaid) % 250 == 0:
                print("Library-parent new complete families freshly replayed", len(newpaid), flush=True)
        files[str(reportpath)] = sha(reportpath)
    assert worker_counts == jobs_report["counts"] and len(outcomes) == len(expected)
    parent = {key: Path(value) for key, value in snapshot["parent_inputs"].items()}
    union, catalogpath, _ = parent_gate(parent["manifest"], parent["terminal"], parent["union"])
    total = union["unique_necessary_weak_graphs"]
    output.mkdir()
    counts, seen = Counter(), set()
    with (basepath / "PAYMENTS.jsonl").open(encoding="ascii") as oldpaid, \
            (basepath / "PENDING.jsonl").open(encoding="ascii") as oldpending, \
            (output / "PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as pending:
        partition = valid_payment_partition(total, oldpaid, oldpending)
        for row in catalog_rows(catalogpath, N, B, total):
            pid, payment, unresolved = next(partition)
            assert pid == row["id"]
            if payment is not None:
                assert pid not in outcomes
                counts[payment["status"]] += 1
            else:
                assert pid in outcomes
                status = outcomes[pid]
                assert (status["centers"], status["faces"]) == (row["centers"], row["faces"])
                assert (unresolved["centers"], unresolved["faces"]) == (row["centers"], row["faces"])
                seen.add(pid)
                payment = newpaid.get(pid)
                if payment is None:
                    counts["pending"] += 1
                    pending.write(json.dumps({"parent_index": pid, "centers": row["centers"],
                                              "faces": row["faces"], "not_paid": True},
                                             separators=(",", ":"))+"\n")
                else:
                    counts["new-strict-complete-filling-family"] += 1
            if payment is not None:
                ledger.write(json.dumps(payment, separators=(",", ":"))+"\n")
        assert next(partition, None) is None
    assert seen == set(outcomes)
    assert counts["strict-exact-weak-graph-exclusion"] == base["counts"]["old-strict-weak-force"]
    assert counts["strict-complete-filling-family-exact-transport"] == base["counts"]["new-strict-exact-outer-family-transport"]
    assert counts["new-strict-complete-filling-family"] == len(newpaid)
    assert len(newpaid)+counts["pending"] == base["remaining_weak_graphs"]
    assert sum(counts.values()) == total
    for path in (Path(__file__).resolve(), snapshotpath, basepath / "VERIFIED.json",
                 basepath / "PAYMENTS.jsonl", basepath / "PENDING.jsonl",
                 stage / "WORKLIST.json", stage / "SUMMARY.json", stage / "INPUT-BINDINGS.json",
                 stage / "COMPLETED-BATCHES.jsonl", controls_path, jobcontrols_path, auditcontrols_path,
                 sourcecontrols_path, constantspath, ROOT / "library_parent_pending_worklist.py",
                 ROOT / "linked_general_collar_kernel.py", ROOT / "audit_complete_origin_fillings.py",
                 ROOT / "audit_complete_origin_finer_supplement.py"):
        files[str(path)] = sha(path)
    for path, oldhash in files.items():
        assert sha(path) == oldhash
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-library-parent-gapped-filling-residual-merge-v1",
        "N": N, "B": B, "complete_parent_weak_graphs": total, "counts": dict(counts),
        "remaining_weak_graphs": counts["pending"], "all_residual_weak_lower_bounds_paid": counts["pending"] == 0,
        "all_complete_parent_indices_partitioned_once": True,
        "all_current_pending_rows_match_genuine_original_snapshot_positions": True,
        "all_new_positive_whole_filling_trees_freshly_mathematically_replayed": True,
        "previous_accepted_weak_library_parent_and_all_its_bound_bytes_rechecked": True,
        "previous_paid_trees_are_prerequisites_not_claimed_replayed_in_this_increment": True,
        "all_library_paid_rows_skipped_by_proposal_workers": True,
        "no_original_snapshot_source_or_schema_identity_forged": True,
        "base_report_sha256": sha(basepath / "VERIFIED.json"),
        "payments_sha256": sha(output / "PAYMENTS.jsonl"), "pending_sha256": sha(output / "PENDING.jsonl"),
        "frozen_files": files, "source_sha256": sha(Path(__file__)),
        "conditional_completions_not_standalone_weak_geometry": True,
        "source_cover_transport_other_families_nonstrict_attainment_and_exact_upper_still_required": True,
        "global_optimality_proved": False,
    })
    print("Complete library-parent incremental filling merge accepted:", dict(counts), flush=True)


if __name__ == "__main__":
    main()
