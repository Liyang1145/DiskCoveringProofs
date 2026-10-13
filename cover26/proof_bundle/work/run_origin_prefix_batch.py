"""Origin-conditioned queue, with explicit reuse only of bound empty subtrees."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import (
    CAPS, SCALE, WORK, Reference, check_frontier, expect_rejection,
    merge_parts, publish, sha,
)
from audit_prefix_origin import OriginReference, OriginRunner
from run_prefix_batch import audit_manifest as audit_legacy
from run_prefix_batch import bound_data, checkpoint, record_only


def command_gate(record, prefix, operation, limit, depth):
    tail = [
        "26", "18", record["path"], str(SCALE), *map(str, CAPS), str(limit),
        "dfs", operation, ",".join(map(str, prefix)) if prefix else "-", str(depth), "1",
    ]
    if record["command"][-14:] != tail:
        raise ValueError("origin launch command mismatch")


def audit_origin_manifest(manifest):
    if not (manifest["N"] == 26 and manifest["B"] == 18
            and manifest["origin_condition_enabled"] is True
            and manifest["global_optimality_proved"] is False
            and manifest["arbitrary_cover_reduction_accepted"] is False):
        raise ValueError("wrong origin job scope")
    for path, digest in manifest["frozen_inputs"].items():
        if sha(path) != digest:
            raise ValueError("changed frozen input: " + path)
    derivation = json.loads(Path(manifest["derivation"]).read_text(encoding="utf-8"))
    if derivation["base_sha256"] != sha(WORK / "peel_synthesis_n26_cap8_prefix.cpp"):
        raise ValueError("origin kernel is not derived from the bound weaker kernel")
    reconstructed = Path(derivation["base_path"]).read_text(encoding="utf-8")
    for edit in derivation["changes"]:
        if reconstructed.count(edit["before"]) != 1:
            raise ValueError("ambiguous source derivation")
        reconstructed = reconstructed.replace(edit["before"], edit["after"])
    if reconstructed != Path(derivation["source_path"]).read_text(encoding="utf-8"):
        raise ValueError("derived source has an unexplained change")
    seed = json.loads(Path(manifest["legacy_checkpoint"]).read_text(encoding="utf-8"))
    legacy = audit_legacy(seed)
    old_records = {
        tuple(event["prefix"]): event["run"]
        for event in seed["events"] if event["kind"] == "closed"
    }
    initial = bound_data(manifest["initial_frontier_run"], 0)
    if not initial["origin_screen"]:
        raise ValueError("initial frontier lacks the origin condition")
    reference = OriginReference(26, 18, "dfs")
    plain = Reference(26, 18, "dfs")
    initial_rows = check_frontier(initial, reference, (), 2)
    pending = {tuple(row["prefix"]): row for row in initial_rows}
    completed = {}
    native_completed = {}
    native_records = []
    reused = limited = refinements = 0
    for event in manifest["events"]:
        prefix = tuple(event["prefix"])
        if prefix not in pending:
            raise ValueError("task processed twice or not in frontier")
        if event["kind"] == "reused_empty":
            if prefix not in legacy["completed"]:
                raise ValueError("reused subtree was not completed by the legacy audit")
            if event["run"] != old_records[prefix]:
                raise ValueError("changed legacy completion record")
            old_data = bound_data(event["run"], 0)
            if old_data["rooted"] or old_data["orbits"] or old_data["survivors"]:
                raise ValueError("cannot reuse a nonempty catalog as empty")
            if plain.resolve(prefix) != reference.resolve(prefix):
                raise ValueError("legacy prefix does not name the same initial state")
            # The mechanical origin derivation only adds an early rejection.
            # From this exact state its outputs are a subset of the old outputs.
            reused += 1
            completed[prefix] = pending.pop(prefix)
        elif event["kind"] == "closed":
            command_gate(event["run"], prefix, "solve", manifest["node_limit"], 0)
            data = bound_data(event["run"], 0)
            if not data["origin_screen"] or data["prefix"] != list(prefix):
                raise ValueError("closed result belongs to a different model")
            completed[prefix] = pending.pop(prefix)
            native_completed[prefix] = completed[prefix]
            native_records.append({**event["run"], "data": data})
        elif event["kind"] in ("split", "refine"):
            if event["kind"] == "split":
                command_gate(event["limited_run"], prefix, "solve", manifest["node_limit"], 0)
                bound_data(event["limited_run"], 1)
                limited += 1
            elif pending[prefix]["child_count"] != 1:
                raise ValueError("forced refinement applied to branching state")
            command_gate(event["frontier_run"], prefix, "frontier", 0, 1)
            data = bound_data(event["frontier_run"], 0)
            if not data["origin_screen"]:
                raise ValueError("split disabled the origin condition")
            rows = check_frontier(data, reference, prefix, 1)
            if not rows or any(len(row["prefix"]) != len(prefix) + 1 for row in rows):
                raise ValueError("split is not a complete immediate-child replacement")
            if event["kind"] == "refine":
                if len(rows) != 1:
                    raise ValueError("forced successor missing")
                refinements += 1
            pending.pop(prefix)
            for row in rows:
                key = tuple(row["prefix"])
                if key in pending or key in completed:
                    raise ValueError("overlapping tasks")
                pending[key] = row
        else:
            raise ValueError("unknown event")
    if manifest["pending_prefixes"] != [list(p) for p in sorted(pending)]:
        raise ValueError("pending frontier lost")
    if manifest["closed_prefixes"] != [list(p) for p in sorted(completed)]:
        raise ValueError("closed frontier changed")
    union = merge_parts(list(native_completed.values()), native_records, 26, 18, "dfs")
    return {
        "pending": pending, "completed": completed, "reused_empty": reused,
        "native_completed": len(native_completed), "limited": limited,
        "forced_refinements": refinements,
        "native_rooted": union["rooted"], "native_orbits": union["orbits"],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--job", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--max-tasks", type=int, default=80)
    parser.add_argument("--node-limit", type=int, default=20000)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--verify-only", action="store_true")
    args = parser.parse_args()
    if args.max_tasks < 1 or args.node_limit < 2:
        raise ValueError("invalid task budget")
    if args.verify_only:
        report = json.loads(args.report.read_text(encoding="utf-8"))
        latest = Path(report["latest_checkpoint"])
        if sha(latest) != report["checkpoint_sha256"]:
            raise ValueError("checkpoint changed")
        manifest = json.loads(latest.read_text(encoding="utf-8"))
        result = audit_origin_manifest(manifest)
        values = (len(result["pending"]), len(result["completed"]), result["reused_empty"],
                  result["native_completed"], result["limited"], result["native_rooted"],
                  result["native_orbits"], result["forced_refinements"])
        fields = ("pending_subtrees", "completed_subtrees", "reused_empty_subtrees",
                  "newly_completed_subtrees", "limited_tasks_split", "closed_rooted_graphs",
                  "closed_distinct_orbits", "forced_nodes_refined")
        if any(report[field] != value for field, value in zip(fields, values)):
            raise ValueError("report overclaims checkpoint")
        print(json.dumps({"fresh_origin_checkpoint_audit_passed": True,
                          **dict(zip(fields, values))}), flush=True)
        return
    if args.report.exists():
        raise FileExistsError(args.report)
    controls_path = WORK.parent / "outputs/n26-origin-screen-controls-v1.json"
    controls = json.loads(controls_path.read_text(encoding="utf-8"))
    if not controls["finite_implementation_checks_verified"]:
        raise ValueError("origin controls not verified")
    for path, digest in controls["files"].items():
        if sha(path) != digest:
            raise ValueError("origin implementation changed after regression")
    if args.resume:
        snapshots = sorted(args.job.glob("checkpoint-*.json"))
        if not snapshots:
            raise ValueError("no origin checkpoint")
        latest = snapshots[-1]
        manifest = json.loads(latest.read_text(encoding="utf-8"))
        if manifest["node_limit"] != args.node_limit:
            raise ValueError("budget changed")
        result = audit_origin_manifest(manifest)
        pending, completed = result["pending"], result["completed"]
        index = int(latest.stem.split("-")[-1]) + 1
    else:
        if args.job.exists():
            raise FileExistsError(args.job)
        args.job.mkdir(parents=True)
        legacy_path = WORK / "b18-prefix-batch-v1/checkpoint-00280.json"
        legacy_manifest = json.loads(legacy_path.read_text(encoding="utf-8"))
        legacy = audit_legacy(legacy_manifest)
        old_records = {
            tuple(event["prefix"]): event["run"]
            for event in legacy_manifest["events"] if event["kind"] == "closed"
        }
        seed = next(
            record for record in controls["native_runs"]
            if "frontier" in record["command"] and "26" in record["command"]
            and record["command"][-2:] == ["2", "1"]
        )
        data = bound_data(seed, 0)
        reference = OriginReference(26, 18, "dfs")
        plain = Reference(26, 18, "dfs")
        rows = check_frontier(data, reference, (), 2)
        pending = {tuple(row["prefix"]): row for row in rows}
        completed, events = {}, []
        for prefix in sorted(legacy["completed"]):
            if prefix not in pending:
                continue  # Deeper old prefixes require a separate explicit transport.
            old_data = bound_data(old_records[prefix], 0)
            if old_data["orbits"] or old_data["rooted"] or old_data["survivors"]:
                continue
            if plain.resolve(prefix) != reference.resolve(prefix):
                continue
            events.append({"kind": "reused_empty", "prefix": list(prefix),
                           "run": old_records[prefix]})
            completed[prefix] = pending.pop(prefix)
        files = dict(controls["files"])
        files.update({
            str(p): sha(p) for p in (
                Path(__file__), controls_path, legacy_path,
                WORK / "run_prefix_batch.py",
                WORK / "prefix-regression-v3/VERIFIED.json",
            )
        })
        manifest = {
            "schema": "N26-B18-origin-prefix-checkpoint-v1", "N": 26, "B": 18,
            "node_limit": args.node_limit, "origin_condition_enabled": True,
            "global_optimality_proved": False,
            "arbitrary_cover_reduction_accepted": False,
            "derivation": str(WORK / "prefix-origin-v1/DERIVATION.json"),
            "legacy_checkpoint": str(legacy_path), "frozen_inputs": files,
            "initial_frontier_run": seed, "events": events,
        }
        latest = args.job / "checkpoint-00000.json"
        checkpoint(latest, manifest, pending, completed)
        audit_origin_manifest(manifest)
        index = 1
        print(json.dumps({"bound_empty_subtrees_reused": len(completed),
                          "initial_pending": len(pending)}), flush=True)

    runner = OriginRunner(args.job)
    runner.serial = 1 + max(
        [int(p.stem.split("-")[-1]) for p in args.job.glob("origin-*.log")], default=-1
    )
    reference = OriginReference(26, 18, "dfs")
    for task in range(args.max_tasks):
        if not pending:
            break
        prefix = min(pending, key=lambda p: (pending[p]["child_count"], -len(p), p))
        if pending[prefix]["child_count"] == 1:
            # Preserve the only successor without repeatedly spending a full
            # node allowance on successive names for the same large subtree.
            cut = runner.run(26, 18, "dfs", 1, "frontier", prefix=prefix, depth=1)
            rows = check_frontier(cut["data"], reference, prefix, 1)
            if len(rows) != 1 or len(rows[0]["prefix"]) != len(prefix) + 1:
                raise ValueError("invalid forced refinement")
            pending.pop(prefix)
            pending[tuple(rows[0]["prefix"])] = rows[0]
            event = {"kind": "refine", "prefix": list(prefix), "frontier_run": record_only(cut)}
        else:
            run = runner.run(26, 18, "dfs", 1, prefix=prefix,
                             limit=args.node_limit, allow_failure=True)
            if run["exit_code"] == 0:
                event = {"kind": "closed", "prefix": list(prefix), "run": record_only(run)}
                completed[prefix] = pending.pop(prefix)
            else:
                bound_data(run, 1)
                cut = runner.run(26, 18, "dfs", 1, "frontier", prefix=prefix, depth=1)
                rows = check_frontier(cut["data"], reference, prefix, 1)
                if not rows or any(len(row["prefix"]) != len(prefix) + 1 for row in rows):
                    raise ValueError("invalid cut")
                pending.pop(prefix)
                for row in rows:
                    pending[tuple(row["prefix"])] = row
                event = {"kind": "split", "prefix": list(prefix),
                         "limited_run": record_only(run), "frontier_run": record_only(cut)}
        manifest["events"].append(event)
        latest = args.job / f"checkpoint-{index:05d}.json"
        checkpoint(latest, manifest, pending, completed)
        index += 1
        if (task + 1) % 10 == 0 or task + 1 == args.max_tasks:
            print(json.dumps({"new_tasks": task + 1, "total_completed": len(completed),
                              "pending": len(pending), "last_event": event["kind"],
                              "prefix": list(prefix)}), flush=True)

    result = audit_origin_manifest(manifest)
    negatives = []
    wrong = deepcopy(manifest)
    wrong["pending_prefixes"].pop()
    expect_rejection("lost-pending-subtree", lambda: audit_origin_manifest(wrong), negatives)
    wrong = deepcopy(manifest)
    wrong["events"].append(wrong["events"][0])
    expect_rejection("duplicate-reuse", lambda: audit_origin_manifest(wrong), negatives)
    wrong = deepcopy(manifest)
    wrong["events"][0]["run"]["exit_code"] = 1
    expect_rejection("nonzero-legacy-exit", lambda: audit_origin_manifest(wrong), negatives)
    wrong = deepcopy(manifest)
    wrong["origin_condition_enabled"] = False
    expect_rejection("changed-origin-model", lambda: audit_origin_manifest(wrong), negatives)
    report = {
        "schema": "N26-B18-origin-conditioned-prefix-progress-v1",
        "verified_partition_bookkeeping": True,
        "origin_condition_enabled": True,
        "arbitrary_cover_reduction_accepted": False,
        "B18_origin_catalog_exhausted": not result["pending"],
        "N26_complete_catalog": False, "global_optimality_proved": False,
        "completed_subtrees": len(result["completed"]),
        "reused_empty_subtrees": result["reused_empty"],
        "newly_completed_subtrees": result["native_completed"],
        "pending_subtrees": len(result["pending"]),
        "limited_tasks_split": result["limited"],
        "forced_nodes_refined": result["forced_refinements"],
        "closed_rooted_graphs": result["native_rooted"],
        "closed_distinct_orbits": result["native_orbits"],
        "latest_checkpoint": str(latest), "checkpoint_sha256": sha(latest),
        "negative_controls_rejected": negatives,
        "frozen_inputs": manifest["frozen_inputs"],
        "scope": "Origin-conditioned combinatorial enumeration, with bound reuse of weaker-model empty subtrees; no global theorem.",
    }
    publish(args.report, report)
    print(json.dumps({k: v for k, v in report.items() if k != "frozen_inputs"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
