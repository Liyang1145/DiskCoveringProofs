"""Immutable actually ended workers only; no incomplete/full-parent scope upgrade."""
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish
from stream_catalog import sha, no_duplicate_keys
from refine_small_order_family import original_gate

assert __debug__


def run(command, output, label):
    with (output / (label+"-STDOUT.log")).open("xb") as stdout, \
            (output / (label+"-STDERR.log")).open("xb") as stderr:
        process = subprocess.Popen(list(map(str, command)), cwd=str(ROOT),
                                   stdout=stdout, stderr=stderr,
                                   env=dict(os.environ, OPENBLAS_NUM_THREADS="1",
                                            OMP_NUM_THREADS="1", MKL_NUM_THREADS="1"),
                                   creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / (label+"-TERMINAL.json"), {
        "pid": process.pid, "actual_exit_code": code, "actual_child_terminal_observed": True,
        "command": list(map(str, command)), "source_sha256": sha(Path(__file__))})
    assert code == 0, ("original refinement child failed; keep evidence", label)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", required=True, type=Path)
    ap.add_argument("--controls", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    ap.add_argument("--force-limit", type=int, default=511)
    ap.add_argument("--skip-parent", type=int, nargs="*", default=[])
    args = ap.parse_args()
    stage, controls_path, output = (
        getattr(args, field).resolve() for field in ("stage", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (stage, controls_path, output))
    assert not output.exists() and 31 < args.force_limit <= 10001
    assert len(args.skip_parent) == len(set(args.skip_parent))
    control = read(controls_path)
    assert control["verified"] and control["schema"] == "small-order-real-full-pending-leaf-refinement-controls-v1"
    assert control["source_sha256"] == sha(ROOT / "test_small_order_refinement.py")
    assert control["refinement_source_sha256"] == sha(ROOT / "refine_small_order_family.py")
    assert control["own_order_real_full_family_strict_positive_separate_process_replayed"]
    assert len(control["wrong_order_constants_source_state_and_topology_refusals"]) == 12
    assert sha(controls_path.parent / "EXACT.json") == control["positive_exact_report_sha256"]
    inputs = read(stage / "INPUT-BINDINGS.json")
    assert inputs["N"] in (23, 24)
    assert inputs["source_sha256"] == sha(ROOT / "small_order_parent_fillings.py")
    frozen = {str(path): sha(path) for path in (
        Path(__file__), controls_path, stage / "INPUT-BINDINGS.json", stage / "PARTITION.json",
        stage / "JOBS.jsonl", ROOT / "small_order_parent_fillings.py",
        ROOT / "refine_small_order_family.py", ROOT / "small_order_filling_kernel.py")}
    selected, completed_jobs, all_pending = [], [], set()
    with (stage / "JOBS.jsonl").open(encoding="ascii") as stream:
        for line in stream:
            descriptor = json.loads(line, object_pairs_hook=no_duplicate_keys)
            ordinal = descriptor["job"]
            directory = stage / f"batch-{ordinal:06}"
            reportpath, terminalpath = directory / "SUMMARY.json", directory / "TERMINAL.json"
            if not reportpath.exists() or not terminalpath.exists():
                continue
            terminal = read(terminalpath)
            assert terminal["actual_exit_code"] == 0 and terminal["actual_child_terminal_observed"]
            assert terminal["source_sha256"] == sha(ROOT / "small_order_parent_fillings.py")
            jobpath = stage / descriptor["job_file"]
            assert sha(jobpath) == descriptor["job_sha256"]
            job, worker = read(jobpath), read(reportpath)
            assert worker["schema"] == "small-order-complete-parent-filling-worker-v1"
            assert worker["source_sha256"] == sha(ROOT / "small_order_parent_fillings.py")
            assert (worker["N"], worker["B"], worker["job"], worker["first"]) == (
                inputs["N"], inputs["B"], ordinal, descriptor["first"])
            assert len(worker["outcomes"]) == len(job["parents"]) == worker["count"] == descriptor["count"]
            completed_jobs.append(ordinal)
            for parent, outcome in zip(job["parents"], worker["outcomes"], strict=True):
                assert (parent["parent_index"], parent["centers"], parent["faces"]) == (
                    outcome["parent_index"], outcome["centers"], outcome["faces"])
                if outcome["status"] != "pending-complete-family":
                    assert outcome["status"] in ("strict-complete-family", "unhandled-source-topology")
                    continue
                pid = parent["parent_index"]
                assert pid not in all_pending
                all_pending.add(pid)
                if pid in args.skip_parent:
                    continue
                # This adapter handles leaf-only debts. A topology frontier
                # would need a separately scoped whole recursive extension.
                if outcome["unsearched_frontier_nodes"]:
                    continue
                family = directory / f"parent-{pid:07}"
                old, accepted, _, _ = original_gate(family)
                assert sha(family / "PROPOSAL.json") == outcome["proof_sha256"]
                assert sha(family / "EXACT.json") == outcome["exact_sha256"]
                collar = read(family / "INPUT-COLLAR.json")
                assert collar["actual_source_parent_index"] == pid
                assert (collar["centers"], collar["faces"]) == (parent["centers"], parent["faces"])
                selected.append({
                    "parent_index": pid, "family": str(family), "job": ordinal,
                    "source_job_sha256": sha(jobpath), "actual_worker_sha256": sha(reportpath),
                    "actual_worker_terminal_sha256": sha(terminalpath)})
                for path in (jobpath, reportpath, terminalpath):
                    frozen[str(path)] = sha(path)
                for path, digest in accepted["frozen_files"].items():
                    assert path not in frozen or frozen[path] == digest
                    frozen[path] = digest
    assert set(args.skip_parent).issubset(all_pending)
    assert selected, "no new eligible actually completed worker debts; no scope upgrade"
    output.mkdir()
    publish(output / "SCOPED-INPUTS.json", {
        "N": inputs["N"], "B": inputs["B"], "selected_families": selected,
        "observed_completed_jobs": completed_jobs, "observed_raw_worker_pending_parents": sorted(all_pending),
        "skipped_explicit_already_replayed_parents": args.skip_parent,
        "not_a_completed_scheduler_or_formal_full_parent_residual": True,
        "original_live_scheduler_and_all_original_math_inputs_unchanged": True,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)), "global_optimality_proved": False})
    outcomes = []
    for item in selected:
        pid, family = item["parent_index"], Path(item["family"])
        proofpath, exactpath = output / f"p{pid}-PROOF.json", output / f"p{pid}-EXACT.json"
        run([sys.executable, "-u", ROOT / "refine_small_order_family.py",
             "--family", family, "--force-limit", args.force_limit, "--output", proofpath],
            output, f"p{pid}-PROPOSE")
        run([sys.executable, "-u", ROOT / "refine_small_order_family.py", "--audit",
             "--family", family, "--refined", proofpath, "--output", exactpath],
            output, f"p{pid}-REPLAY")
        accepted = read(exactpath)
        assert accepted["verified"]
        outcomes.append({
            **item, "whole_family_strictly_closed": accepted["whole_completion_family_strictly_closed"],
            "proof_path": str(proofpath), "exact_path": str(exactpath),
            "proof_sha256": sha(proofpath), "exact_sha256": sha(exactpath),
            "pending_complete_leaves": accepted["pending_complete_leaves"],
            "unsearched_frontier_nodes": accepted["unsearched_frontier_nodes"]})
        print("Own-order actually completed worker deeper family", pid, "whole strict",
              accepted["whole_completion_family_strictly_closed"],
              len(outcomes), "/", len(selected), flush=True)
    for path, digest in frozen.items():
        assert sha(path) == digest
    publish(output / "SUMMARY.json", {
        "N": inputs["N"], "B": inputs["B"], "outcomes": outcomes,
        "selected_families": len(selected),
        "whole_families_strictly_closed": sum(item["whole_family_strictly_closed"] for item in outcomes),
        "all_actual_independent_children_successful_terminals_observed": True,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "complete_actual_source_parent_adoption_not_performed_here": True,
        "global_optimality_proved": False})


if __name__ == "__main__":
    main()
