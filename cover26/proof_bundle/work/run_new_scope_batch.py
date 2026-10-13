"""Fresh-threshold adaptive queue for B=14..17; no legacy prefix reuse.

Each node-limited subtree is replaced by ALL independently checked immediate
children. Completed catalogs are merged by graph union, never by orbit sum.
"""

import argparse
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import time

from audit_prefix_partition import (
    WORK, check_frontier, expect_rejection, merge_parts, native_command, publish,
)
from audit_prefix_origin import OriginReference, validate_disk
from new_upper_scope import sha as original_sha
from run_prefix_batch import bound_data, checkpoint, record_only


def sha(path):
    return original_sha(str(path).replace("\\", "/"))


def command_gate(record, manifest, prefix, operation, limit, depth):
    tail = ["26", str(manifest["B"]), record["path"], str(manifest["scale"]),
            *map(str, manifest["caps"]), str(limit), "dfs", operation,
            ",".join(map(str, prefix)) if prefix else "-", str(depth), "1"]
    if record["command"][-14:] != tail:
        raise ValueError("launch does not name the bound fresh-scope subtree")


def audit(manifest):
    b, caps, scale = manifest["B"], manifest["caps"], manifest["scale"]
    if not (manifest["N"] == 26 and b in (14, 15, 16, 17)
            and manifest["origin_condition_enabled"] is True
            and manifest["global_optimality_proved"] is False
            and manifest["arbitrary_cover_reduction_accepted"] is False):
        raise ValueError("wrong queue scope")
    for path, digest in manifest["frozen_inputs"].items():
        if sha(path) != digest:
            raise ValueError("changed frozen queue input: " + path)
    constants = json.loads(Path(manifest["constants_path"]).read_text())
    if (caps, scale) != (constants["angle_caps"], constants["angle_scale"]):
        raise ValueError("mixed new/old angle budget")
    initial_path = Path(manifest["initial_frontier_path"])
    if sha(initial_path) != manifest["initial_frontier_sha256"]:
        raise ValueError("changed initial frontier")
    reference = OriginReference(26, b, "dfs", caps=caps, scale=scale)
    initial = json.loads(initial_path.read_text())
    if not initial["origin_screen"]:
        raise ValueError("missing initial origin condition")
    rows = check_frontier(initial, reference, (), 2)
    pending = {tuple(row["prefix"]): row for row in rows}
    completed, records = {}, []
    splits = refinements = 0
    for event in manifest["events"]:
        prefix = tuple(event["prefix"])
        if prefix not in pending:
            raise ValueError("event lost, duplicated, or outside current partition")
        kind = event["kind"]
        if kind == "closed":
            record = event["run"]
            command_gate(record, manifest, prefix, "solve", manifest["node_limit"], 0)
            data = bound_data(record, 0)
            if not data["origin_screen"] or data["prefix"] != list(prefix):
                raise ValueError("completion uses a different origin model/prefix")
            for graph in data["survivors"]:
                validate_disk(26, b, graph["faces"])
            completed[prefix] = pending.pop(prefix)
            records.append({**record, "data": data})
        elif kind in ("split", "refine"):
            if kind == "split":
                command_gate(event["limited_run"], manifest, prefix, "solve", manifest["node_limit"], 0)
                bound_data(event["limited_run"], 1)
                splits += 1
            else:
                if pending[prefix]["child_count"] != 1:
                    raise ValueError("forced refinement is not forced")
                refinements += 1
            record = event["frontier_run"]
            command_gate(record, manifest, prefix, "frontier", 0, 1)
            data = bound_data(record, 0)
            if not data["origin_screen"]:
                raise ValueError("split changed origin model")
            children = check_frontier(data, reference, prefix, 1)
            if not children or any(len(row["prefix"]) != len(prefix) + 1 for row in children):
                raise ValueError("not an exhaustive immediate-child replacement")
            pending.pop(prefix)
            for row in children:
                key = tuple(row["prefix"])
                if key in pending or key in completed:
                    raise ValueError("overlapping replacement")
                pending[key] = row
        else:
            raise ValueError("unknown event")
    if manifest["pending_prefixes"] != [list(p) for p in sorted(pending)]:
        raise ValueError("pending partition changed")
    if manifest["closed_prefixes"] != [list(p) for p in sorted(completed)]:
        raise ValueError("closed partition changed")
    union = merge_parts(list(completed.values()), records, 26, b, "dfs", caps=caps, scale=scale)
    return {"pending": pending, "completed": completed, "union": union,
            "splits": splits, "refinements": refinements}


class Runner:
    def __init__(self, job, manifest):
        self.job, self.manifest = job, manifest
        self.serial = 1 + max([int(p.stem.split("-")[-1]) for p in job.glob("run-*.log")],
                              default=-1)

    def run(self, prefix, operation="solve", depth=0, limit=0):
        m = self.manifest
        path = self.job / f"run-{self.serial:05d}.json"
        log = self.job / f"run-{self.serial:05d}.log"
        self.serial += 1
        command = native_command(WORK / "prefix-origin-v1/peel_prefix_origin.linux", [
            "26", str(m["B"]), str(path), str(m["scale"]), *map(str, m["caps"]),
            str(limit), "dfs", operation, ",".join(map(str, prefix)) if prefix else "-",
            str(depth), "1"])
        start = time.monotonic()
        result = subprocess.run(command, capture_output=True, timeout=90)
        log.write_bytes(result.stdout + result.stderr)
        record = {"path": str(path), "log": str(log), "log_sha256": sha(log),
                  "exit_code": result.returncode, "command": command,
                  "seconds": time.monotonic() - start}
        if not result.returncode:
            record["sha256"] = sha(path)
            record["data"] = bound_data(record, 0)
        else:
            bound_data(record, 1)
        return record


def report_values(result):
    return {"completed_subtrees": len(result["completed"]),
            "pending_subtrees": len(result["pending"]),
            "closed_rooted_graphs": result["union"]["rooted"],
            "closed_distinct_orbits": result["union"]["orbits"],
            "limited_tasks_split_not_excluded": result["splits"],
            "forced_nodes_refined": result["refinements"],
            "restricted_family_catalog_exhausted": not result["pending"]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--job", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--b", type=int, required=True, choices=(14, 15, 16, 17))
    parser.add_argument("--max-tasks", type=int, default=40)
    parser.add_argument("--node-limit", type=int, default=20000)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--verify-only", action="store_true")
    args = parser.parse_args()
    if args.verify_only:
        report = json.loads(args.report.read_text())
        path = Path(report["latest_checkpoint"])
        if sha(path) != report["checkpoint_sha256"]:
            raise ValueError("checkpoint changed")
        manifest = json.loads(path.read_text())
        if manifest["B"] != args.b:
            raise ValueError("wrong family")
        result = audit(manifest)
        if any(report[k] != v for k, v in report_values(result).items()):
            raise ValueError("report overclaims the audited checkpoint")
        print(json.dumps({"fresh_content_recheck_passed": True, **report_values(result)}), flush=True)
        return
    if args.report.exists() or args.max_tasks < 1 or args.node_limit < 2:
        raise ValueError("fresh report and valid budgets required")
    if args.resume:
        snapshots = sorted(args.job.glob("checkpoint-*.json"))
        if not snapshots:
            raise ValueError("no checkpoint to resume")
        latest = snapshots[-1]
        manifest = json.loads(latest.read_text())
        if manifest["B"] != args.b or manifest["node_limit"] != args.node_limit:
            raise ValueError("family/node budget changed")
        result = audit(manifest)
        pending, completed = result["pending"], result["completed"]
        index = int(latest.stem.split("-")[-1]) + 1
    else:
        if args.job.exists():
            raise FileExistsError(args.job)
        scope = WORK.parent / "outputs/n26-new-scope-v1"
        frontier_dir = WORK.parent / "outputs/n26-new-scope-frontiers-v1"
        gate_path = frontier_dir / "VERIFIED.json"
        gate = json.loads(gate_path.read_text())
        if not gate["frontier_generation_and_independent_reconstruction_verified"]:
            raise ValueError("new frontiers unaccepted")
        for path, digest in gate["files"].items():
            if sha(path) != digest:
                raise ValueError("changed new-frontier dependency")
        constants_path = scope / "CONSTANTS.json"
        constants = json.loads(constants_path.read_text())
        entry = next(row for row in gate["families"] if row["B"] == args.b)
        initial_path = Path(entry["frontier_path"])
        initial = json.loads(initial_path.read_text())
        reference = OriginReference(26, args.b, "dfs", caps=constants["angle_caps"],
                                    scale=constants["angle_scale"])
        rows = check_frontier(initial, reference, (), 2)
        frozen = dict(gate["files"])
        frozen.update({str(path): sha(path) for path in (
            Path(__file__), WORK / "run_prefix_batch.py", gate_path, constants_path,
            initial_path)})
        manifest = {
            "schema": "N26-new-threshold-adaptive-prefix-checkpoint-v1",
            "N": 26, "B": args.b, "node_limit": args.node_limit,
            "caps": constants["angle_caps"], "scale": constants["angle_scale"],
            "origin_condition_enabled": True, "global_optimality_proved": False,
            "arbitrary_cover_reduction_accepted": False,
            "constants_path": str(constants_path),
            "initial_frontier_path": str(initial_path),
            "initial_frontier_sha256": entry["frontier_sha256"],
            "frozen_inputs": frozen, "events": []}
        pending = {tuple(row["prefix"]): row for row in rows}
        completed = {}
        args.job.mkdir(parents=True)
        latest = args.job / "checkpoint-00000.json"
        checkpoint(latest, manifest, pending, completed)
        audit(manifest)
        index = 1
    runner = Runner(args.job, manifest)
    reference = OriginReference(26, args.b, "dfs", caps=manifest["caps"], scale=manifest["scale"])
    for task in range(args.max_tasks):
        if not pending:
            break
        prefix = min(pending, key=lambda p: (pending[p]["child_count"], -len(p), p))
        if pending[prefix]["child_count"] == 1:
            cut = runner.run(prefix, "frontier", depth=1)
            rows = check_frontier(cut["data"], reference, prefix, 1)
            if len(rows) != 1:
                raise ValueError("wrong forced successor")
            event = {"kind": "refine", "prefix": list(prefix), "frontier_run": record_only(cut)}
        else:
            run = runner.run(prefix, limit=args.node_limit)
            if not run["exit_code"]:
                completed[prefix] = pending.pop(prefix)
                event = {"kind": "closed", "prefix": list(prefix), "run": record_only(run)}
            else:
                cut = runner.run(prefix, "frontier", depth=1)
                rows = check_frontier(cut["data"], reference, prefix, 1)
                if not rows or any(len(row["prefix"]) != len(prefix) + 1 for row in rows):
                    raise ValueError("wrong adaptive replacement")
                event = {"kind": "split", "prefix": list(prefix),
                         "limited_run": record_only(run), "frontier_run": record_only(cut)}
        if event["kind"] != "closed":
            pending.pop(prefix)
            for row in rows:
                key = tuple(row["prefix"])
                if key in pending or key in completed:
                    raise ValueError("overlapping replacement")
                pending[key] = row
        manifest["events"].append(event)
        latest = args.job / f"checkpoint-{index:05d}.json"
        checkpoint(latest, manifest, pending, completed)
        index += 1
        if (task + 1) % 10 == 0 or task + 1 == args.max_tasks:
            print(json.dumps({"B": args.b, "tasks_this_run": task + 1,
                              "completed_subtrees": len(completed), "pending_subtrees": len(pending),
                              "last_event": event["kind"], "last_prefix": list(prefix)}), flush=True)
    result = audit(manifest)
    negatives = []
    wrong = deepcopy(manifest)
    wrong["events"].pop()
    expect_rejection("omitted-event", lambda: audit(wrong), negatives)
    wrong = deepcopy(manifest)
    wrong["events"].append(wrong["events"][0])
    expect_rejection("duplicate-event", lambda: audit(wrong), negatives)
    wrong = deepcopy(manifest)
    wrong["caps"][0] += 1
    expect_rejection("changed-angle-budget", lambda: audit(wrong), negatives)
    wrong = deepcopy(manifest)
    wrong["global_optimality_proved"] = True
    expect_rejection("false-global-completion", lambda: audit(wrong), negatives)
    if manifest["pending_prefixes"]:
        wrong = deepcopy(manifest)
        wrong["pending_prefixes"].pop()
        expect_rejection("lost-pending-subtree", lambda: audit(wrong), negatives)
    report = {
        "schema": "N26-new-threshold-adaptive-prefix-progress-v1", "N": 26, "B": args.b,
        "verified_partition_bookkeeping": True, **report_values(result),
        "N26_complete_catalog": False, "global_optimality_proved": False,
        "arbitrary_cover_reduction_accepted": False,
        "latest_checkpoint": str(latest), "checkpoint_sha256": sha(latest),
        "negative_controls_rejected": negatives, "frozen_inputs": manifest["frozen_inputs"],
        "scope": "Restricted combinatorial subtree catalogs only; nonempty survivors are not geometric exclusions.",
    }
    publish(args.report, report)
    print(json.dumps({k: v for k, v in report.items() if k != "frozen_inputs"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
