"""Bounded, checkpointed subtree enumeration. Pending work is never discarded."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import (
    CAPS, SCALE, WORK, Reference, Runner, check_frontier, expect_rejection,
    merge_parts, publish, sha,
)


def record_only(record):
    return {key: value for key, value in record.items() if key != "data"}


def bound_data(record, expected_exit):
    if record["exit_code"] != expected_exit:
        raise ValueError("incorrect terminal exit")
    if sha(record["log"]) != record["log_sha256"]:
        raise ValueError("changed process log")
    if expected_exit:
        if Path(record["path"]).exists():
            raise ValueError("incomplete run published output")
        if "REJECTED NODE LIMIT:" not in Path(record["log"]).read_text(encoding="utf-8"):
            raise ValueError("non-limit failure is not a splittable subtree")
        return None
    if sha(record["path"]) != record["sha256"]:
        raise ValueError("changed result")
    return json.loads(Path(record["path"]).read_text(encoding="utf-8"))


def check_command(record, prefix, operation, limit, depth):
    command = record["command"]
    expected_tail = [
        "26", "18", record["path"], str(SCALE), *map(str, CAPS), str(limit),
        "dfs", operation, ",".join(map(str, prefix)) if prefix else "-", str(depth),
    ]
    # Production runs are hosted inside WSL; the bound paths are already POSIX.
    if command[-13:] != expected_tail:
        raise ValueError("launch command disagrees with named subtree")


def audit_manifest(manifest):
    if not (manifest["N"] == 26 and manifest["B"] == 18
            and manifest["global_optimality_proved"] is False
            and manifest["arbitrary_cover_reduction_proved"] is False):
        raise ValueError("wrong manifest scope")
    for path, digest in manifest["frozen_inputs"].items():
        if sha(path) != digest:
            raise ValueError("changed frozen input: " + path)
    initial = bound_data(manifest["initial_frontier_run"], 0)
    reference = Reference(26, 18, "dfs")
    rows = check_frontier(initial, reference, (), 2)
    pending = {tuple(row["prefix"]): row for row in rows}
    completed = {}
    closed_records = []
    limited_count = 0
    for event in manifest["events"]:
        prefix = tuple(event["prefix"])
        if prefix not in pending:
            raise ValueError("event outside pending partition or processed twice")
        if event["kind"] == "closed":
            record = event["run"]
            check_command(record, prefix, "solve", manifest["node_limit"], 0)
            data = bound_data(record, 0)
            if data["prefix"] != list(prefix):
                raise ValueError("closed result belongs to another subtree")
            completed[prefix] = pending.pop(prefix)
            closed_records.append({**record, "data": data})
        elif event["kind"] == "split":
            limited = event["limited_run"]
            check_command(limited, prefix, "solve", manifest["node_limit"], 0)
            bound_data(limited, 1)
            limited_count += 1
            frontier_record = event["frontier_run"]
            check_command(frontier_record, prefix, "frontier", 0, 1)
            data = bound_data(frontier_record, 0)
            children = check_frontier(data, reference, prefix, 1)
            if not children or any(len(row["prefix"]) != len(prefix) + 1 for row in children):
                raise ValueError("failed subtree not replaced by all immediate children")
            pending.pop(prefix)
            for child in children:
                key = tuple(child["prefix"])
                if key in pending or key in completed:
                    raise ValueError("overlapping partition")
                pending[key] = child
        else:
            raise ValueError("unknown event")
    if manifest["pending_prefixes"] != [list(path) for path in sorted(pending)]:
        raise ValueError("pending frontier lost or changed")
    if manifest["closed_prefixes"] != [list(path) for path in sorted(completed)]:
        raise ValueError("completed partition lost or changed")
    merged = merge_parts(list(completed.values()), closed_records, 26, 18, "dfs")
    return {
        "pending": pending, "completed": completed,
        "closed_rooted": merged["rooted"], "closed_distinct_orbits": merged["orbits"],
        "node_limited_tasks_split_not_excluded": limited_count,
    }


def checkpoint(path, manifest, pending, completed):
    manifest["pending_prefixes"] = [list(p) for p in sorted(pending)]
    manifest["closed_prefixes"] = [list(p) for p in sorted(completed)]
    publish(path, manifest)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--job", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--max-tasks", type=int, default=80)
    parser.add_argument("--node-limit", type=int, default=20000)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    if args.max_tasks < 1 or args.node_limit < 2:
        raise ValueError("invalid budget")
    qa_path = WORK / "prefix-regression-v3" / "VERIFIED.json"
    qa = json.loads(qa_path.read_text(encoding="utf-8"))
    if not qa["verified_implementation_tests"] or len(qa["negative_controls_rejected"]) < 18:
        raise ValueError("required partition controls absent")
    for path, digest in qa["files"].items():
        if sha(path) != digest:
            raise ValueError("partition implementation changed since regression")
    real = next(record for record in qa["runs"]
                if "frontier" in record["command"] and "26" in record["command"]
                and record["command"][-1] == "2")
    if args.resume:
        snapshots = sorted(args.job.glob("checkpoint-*.json"))
        if not snapshots:
            raise ValueError("no checkpoint to resume")
        latest = snapshots[-1]
        manifest = json.loads(latest.read_text(encoding="utf-8"))
        if manifest["node_limit"] != args.node_limit:
            raise ValueError("changing budget requires a distinct job")
        audited = audit_manifest(manifest)
        pending, completed = audited["pending"], audited["completed"]
        checkpoint_index = int(latest.stem.split("-")[-1]) + 1
    else:
        if args.job.exists():
            raise FileExistsError(args.job)
        args.job.mkdir(parents=True)
        reference = Reference(26, 18, "dfs")
        data = bound_data(real, 0)
        rows = check_frontier(data, reference, (), 2)
        pending = {tuple(row["prefix"]): row for row in rows}
        completed = {}
        manifest = {
            "schema": "N26-B18-prefix-partition-checkpoint-v1", "N": 26, "B": 18,
            "node_limit": args.node_limit,
            "global_optimality_proved": False, "arbitrary_cover_reduction_proved": False,
            "frozen_inputs": {
                str(path): sha(path) for path in (
                    Path(__file__), WORK / "audit_prefix_partition.py",
                    WORK / "peel_synthesis_n26_cap8_prefix.cpp",
                    WORK / "peel_prefix_v1.linux", qa_path,
                )
            },
            "initial_frontier_run": real, "events": [],
        }
        checkpoint(args.job / "checkpoint-00000.json", manifest, pending, completed)
        checkpoint_index = 1
    runner = Runner(args.job, WORK / "peel_prefix_v1.linux")
    runner.serial = 1 + max(
        [int(path.stem.split("-")[-1]) for path in args.job.glob("run-*.log")], default=-1
    )
    reference = Reference(26, 18, "dfs")
    for task_number in range(args.max_tasks):
        if not pending:
            break
        # Close known empty subtrees first; otherwise descend into the narrowest
        # pending node. Every unchosen sibling remains in the checkpoint.
        prefix = min(pending, key=lambda p: (pending[p]["child_count"], -len(p), p))
        run = runner.run(26, 18, "dfs", prefix=prefix,
                         limit=args.node_limit, allow_failure=True)
        if run["exit_code"] == 0:
            completed[prefix] = pending.pop(prefix)
            event = {"kind": "closed", "prefix": list(prefix), "run": record_only(run)}
        else:
            bound_data(run, 1)
            frontier_run = runner.run(26, 18, "dfs", "frontier", prefix=prefix, depth=1)
            rows = check_frontier(frontier_run["data"], reference, prefix, 1)
            if not rows or any(len(row["prefix"]) != len(prefix) + 1 for row in rows):
                raise ValueError("invalid adaptive cut")
            pending.pop(prefix)
            for row in rows:
                pending[tuple(row["prefix"])] = row
            event = {"kind": "split", "prefix": list(prefix),
                     "limited_run": record_only(run), "frontier_run": record_only(frontier_run)}
        manifest["events"].append(event)
        latest = args.job / f"checkpoint-{checkpoint_index:05d}.json"
        checkpoint(latest, manifest, pending, completed)
        checkpoint_index += 1
        if (task_number + 1) % 10 == 0 or task_number + 1 == args.max_tasks:
            print(json.dumps({"tasks_this_run": task_number + 1, "closed_subtrees": len(completed),
                              "pending_subtrees": len(pending), "last_event": event["kind"],
                              "last_prefix": list(prefix)}), flush=True)

    audited = audit_manifest(manifest)
    negatives = []
    changed = deepcopy(manifest)
    changed["pending_prefixes"].pop()
    expect_rejection("lost-pending-frontier", lambda: audit_manifest(changed), negatives)
    changed = deepcopy(manifest)
    changed["events"].pop()
    expect_rejection("omitted-search-event", lambda: audit_manifest(changed), negatives)
    changed = deepcopy(manifest)
    changed["events"].append(changed["events"][0])
    expect_rejection("duplicate-search-event", lambda: audit_manifest(changed), negatives)
    changed = deepcopy(manifest)
    changed["events"][0]["run"]["exit_code"] = 1
    expect_rejection("false-completion-from-nonzero-exit", lambda: audit_manifest(changed), negatives)
    report = {
        "schema": "N26-B18-adaptive-prefix-progress-audit-v1",
        "verified_partition_bookkeeping": True,
        "global_optimality_proved": False,
        "arbitrary_cover_reduction_proved": False,
        "N26_complete_catalog": False,
        "B18_enumeration_complete": not audited["pending"],
        "initial_depth2_subtrees": 775,
        "enumeration_completed_subtrees": len(audited["completed"]),
        "pending_subtrees_retained": len(audited["pending"]),
        "closed_subtree_rooted_graphs": audited["closed_rooted"],
        "closed_subtree_distinct_orbits": audited["closed_distinct_orbits"],
        "node_limited_tasks_split_not_excluded": audited["node_limited_tasks_split_not_excluded"],
        "events_observed": len(manifest["events"]),
        "latest_checkpoint": str(latest), "checkpoint_sha256": sha(latest),
        "negative_controls_rejected": negatives,
        "frozen_inputs": manifest["frozen_inputs"],
        "scope": "Exhaustion of named combinatorial subtrees and exact preservation of the remaining frontier, not a geometric lower bound.",
    }
    publish(args.report, report)
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ("frozen_inputs", "scope")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
