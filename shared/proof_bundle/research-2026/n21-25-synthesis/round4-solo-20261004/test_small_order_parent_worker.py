"""Actual completed-parent worker controls; never claim a two-row full family."""
from pathlib import Path
from copy import deepcopy
import argparse
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish
from stream_catalog import sha
from small_order_parent_fillings import parent_gate, pending_rows, controls_gate, worker
from replay_small_order_filling import replay

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    controls = ROOT / "small-order-filling-controls-v2/VERIFIED.json"
    controls_gate(controls)
    stage, lower = ROOT / "n24-B16-s1", ROOT / "n24-B16-l1"
    source, report = parent_gate(stage, lower)
    iterator = pending_rows(lower, report["pending_weak_graphs"])
    selected = [next(iterator), next(iterator)]
    iterator.close()
    output.mkdir()
    job = {
        "schema": "small-order-actual-parent-residual-filling-job-v1", "N": 24, "B": 16,
        "job": 0, "first": 0, "parents": selected,
        "controls_path": str(controls),
        "source_acceptance_sha256": sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json"),
        "lower_report_sha256": sha(lower / "ACCEPTED/VERIFIED.json"),
        "constants_sha256": sha(ROOT.parent / "evidence/core-reduction/constants/n24.json"),
        "topology_limit": 10000, "force_limit": 31,
        "source_sha256": sha(ROOT / "small_order_parent_fillings.py"),
        "CONTROL_ONLY_TWO_ACTUAL_ROWS_NOT_ENTIRE_PARENT": True}
    jobpath, work = output / "JOB.json", output / "WORKER"
    publish(jobpath, job)
    command = [sys.executable, "-u", str(ROOT / "small_order_parent_fillings.py"),
               "--worker", str(jobpath), "--output", str(work)]
    with (output / "STDOUT.log").open("xb") as stdout, \
            (output / "STDERR.log").open("xb") as stderr:
        process = subprocess.Popen(
            command, cwd=str(ROOT), stdout=stdout, stderr=stderr,
            env=dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1"),
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / "TERMINAL.json", {
        "actual_exit_code": code, "pid": process.pid, "actual_child_terminal_observed": True})
    assert code == 0, (output / "STDERR.log").read_text()
    summary = read(work / "SUMMARY.json")
    assert [outcome["parent_index"] for outcome in summary["outcomes"]] == [
        row["parent_index"] for row in selected]
    replays = []
    for original, outcome in zip(selected, summary["outcomes"], strict=True):
        family = work / f"parent-{original['parent_index']:07}"
        assert outcome["status"] != "unhandled-source-topology"
        fresh = replay(family / "INPUT-COLLAR.json", family / "PROPOSAL.json")
        assert fresh == read(family / "EXACT.json")
        assert fresh["whole_completion_family_strictly_closed"] == (
            outcome["status"] == "strict-complete-family")
        replays.append({"parent_index": original["parent_index"],
                        "whole_family_strictly_closed": fresh["whole_completion_family_strictly_closed"],
                        "fresh_exact_report_sha256": sha(family / "EXACT.json")})
    refusals = []
    for field, value in (("schema", "complete-parent-pending-filling-worker-v1"),
                         ("N", 25), ("constants_sha256", "0"*64),
                         ("source_sha256", "0"*64)):
        bad = deepcopy(job)
        bad[field] = value
        path = output / ("BAD-"+field+".json")
        publish(path, bad)
        try:
            worker(path, output / ("BAD-"+field+"-OUTPUT"))
        except (AssertionError, KeyError):
            refusals.append(field)
        else:
            raise AssertionError("bad worker input accepted: "+field)
    assert len(selected) < report["pending_weak_graphs"]
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "small-order-actual-parent-worker-controls-v1",
        "actual_parent_rows": replays, "separate_worker_and_family_replay_terminals_observed": True,
        "wrong_order_source_and_constant_controls_rejected": refusals,
        "not_a_complete_parent_partition_or_adoption": True,
        "source_sha256": sha(Path(__file__)),
        "worker_source_sha256": sha(ROOT / "small_order_parent_fillings.py"),
        "family_controls_sha256": sha(controls),
        "worker_report_sha256": sha(work / "SUMMARY.json"), "global_optimality_proved": False})
    print("Own-order parent worker controls passed: two actual residual families,",
          len(refusals), "refusals; no whole-parent payment", flush=True)


if __name__ == "__main__":
    main()
