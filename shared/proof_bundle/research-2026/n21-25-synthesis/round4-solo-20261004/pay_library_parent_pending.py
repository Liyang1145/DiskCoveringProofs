"""Original frozen workers on explicit residual ranges; no old-schema forgery."""
from pathlib import Path
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import read, publish
from library_parent_pending_worklist import select, consecutive_jobs
from pay_complete_origin_pending import gate, invoke

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("snapshot", "base", "controls", "job-controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--batch-size", type=int, default=128)
    ap.add_argument("--limit", type=int, default=10000)
    ap.add_argument("--force-limit", type=int, default=31)
    args = ap.parse_args()
    snapshotpath, basepath, controlpath, jobcontrolpath, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("snapshot", "base", "controls", "job-controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (snapshotpath, basepath, controlpath, jobcontrolpath, output))
    assert not output.exists() and 1 <= args.workers <= 8
    assert 1 <= args.limit <= 100000 and 1 <= args.force_limit <= 1001
    tested = read(jobcontrolpath)
    assert tested["verified"] and tested["schema"] == "original-snapshot-gapped-job-partition-controls-v1"
    assert tested["source_sha256"] == sha(ROOT / "test_library_parent_gapped_jobs.py")
    assert tested["selection_source_sha256"] == sha(ROOT / "library_parent_pending_worklist.py")
    snapshot, base, selected = select(snapshotpath, basepath)
    oldsnapshot, frozen = gate(snapshotpath, controlpath)
    assert snapshot == oldsnapshot
    positions = [row["snapshot_position"] for row in selected]
    jobs = consecutive_jobs(positions, args.batch_size)
    for path in (Path(__file__).resolve(), basepath / "VERIFIED.json", basepath / "PAYMENTS.jsonl",
                 basepath / "PENDING.jsonl", jobcontrolpath, ROOT / "library_parent_pending_worklist.py"):
        frozen[str(path)] = sha(path)
    output.mkdir()
    publish(output / "WORKLIST.json", {
        "schema": "accepted-library-parent-original-root-snapshot-residual-worklist-v1",
        "N": snapshot["N"], "B": snapshot["B"], "entries": selected, "jobs": jobs,
        "source_root_snapshot_sha256": sha(snapshotpath),
        "accepted_library_parent_sha256": sha(basepath / "VERIFIED.json"),
        "original_root_snapshot_unchanged_and_not_relabelled": True,
        "all_current_library_parent_pending_rows_compared_against_full_catalog": True,
        "all_library_paid_source_positions_skipped": True,
        "not_a_discovery_or_partial_native_search": True, "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)), "new_payments_not_proved_by_worklist": True,
        "global_optimality_proved": False,
    })
    publish(output / "INPUT-BINDINGS.json", {
        "N": snapshot["N"], "B": snapshot["B"], "workers": args.workers,
        "selected_original_pending_graphs": len(selected), "original_root_snapshot_graphs": len(snapshot["graphs"]),
        "snapshot_sha256": sha(snapshotpath), "base_report_sha256": sha(basepath / "VERIFIED.json"),
        "worklist_sha256": sha(output / "WORKLIST.json"), "frozen_files": frozen,
        "all_original_worker_sources_and_true_snapshot_schema_preserved": True,
        "global_optimality_proved": False,
    })

    def job(descriptor):
        directory = output / f"batch-{descriptor['job']:06}"
        logs = output / f"logs-{descriptor['job']:06}"
        logs.mkdir()
        code = invoke(ROOT / "pay_complete_origin_pending.py", [
            "--snapshot", snapshotpath, "--controls", controlpath, "--output", directory,
            "--worker-first", descriptor["first"], "--worker-count", descriptor["count"],
            "--limit", args.limit, "--force-limit", args.force_limit], logs, "WORKER", frozen)
        assert code == 0, ("original worker failed; outputs retained", descriptor)
        reportpath = directory / "SUMMARY.json"
        report = read(reportpath)
        assert report["schema"] == "complete-parent-pending-filling-worker-v1"
        assert report["source_sha256"] == sha(ROOT / "pay_complete_origin_pending.py")
        assert report["snapshot_sha256"] == sha(snapshotpath)
        assert (report["first"], report["count"]) == (descriptor["first"], descriptor["count"])
        expected = selected[descriptor["selected_offset"]:descriptor["selected_offset"]+descriptor["count"]]
        assert len(report["outcomes"]) == len(expected)
        for actual, wanted in zip(report["outcomes"], expected, strict=True):
            assert (actual["parent_index"], actual["centers"], actual["faces"]) == (
                wanted["parent_index"], wanted["centers"], wanted["faces"])
        return {**descriptor, "worker_report_sha256": sha(reportpath),
                "counts": dict(Counter(row["status"] for row in report["outcomes"]))}

    processed, counts = 0, Counter()
    todo = iter(jobs)
    with (output / "COMPLETED-BATCHES.jsonl").open("x", encoding="ascii") as ledger:
        with ThreadPoolExecutor(max_workers=args.workers) as executor:
            active = {executor.submit(job, descriptor) for descriptor in
                      [next(todo) for _ in range(min(args.workers, len(jobs)))]}
            while active:
                done, active = wait(active, return_when=FIRST_COMPLETED)
                for future in done:
                    result = future.result()
                    ledger.write(json.dumps(result, separators=(",", ":"))+"\n")
                    ledger.flush()
                    processed += result["count"]
                    counts.update(result["counts"])
                    print("Library-parent true original residual worker progress", processed, "/", len(selected),
                          dict(counts), flush=True)
                    descriptor = next(todo, None)
                    if descriptor is not None:
                        active.add(executor.submit(job, descriptor))
    assert processed == len(selected)
    for path, digest in frozen.items():
        assert sha(path) == digest
    publish(output / "SUMMARY.json", {
        "scheduler_completed": True, "schema": "library-parent-gapped-original-snapshot-filling-jobs-v1",
        "N": snapshot["N"], "B": snapshot["B"], "selected_graphs": processed, "counts": dict(counts),
        "job_count": len(jobs), "worklist_sha256": sha(output / "WORKLIST.json"),
        "completed_batches_sha256": sha(output / "COMPLETED-BATCHES.jsonl"),
        "source_sha256": sha(Path(__file__)),
        "all_original_worker_sources_and_true_snapshot_schema_preserved": True,
        "all_old_library_paid_rows_skipped_not_reproved": True,
        "independent_full_parent_merge_still_required": True, "global_optimality_proved": False,
    })
    print("Library-parent original gapped workers finished; full-parent proof merge still required", dict(counts), flush=True)


if __name__ == "__main__":
    main()
