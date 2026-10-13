"""Deepen only the genuine previous proposal-pending complete B14 types."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
import argparse
import gzip
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from audit_n23_B14_full_residual import parent_gate
from audit_n23_B14_selected_full_supplements import select_actual_proposal_pending
from audit_n23_B14_pending_outer import IndexedOriginal
from audit_n23_B15_effective_outer_payment import pending_indices
from probe_collar_batches import make
import exact_graph as exact

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("source", "original-parent", "previous-stage", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--limit", type=int, default=511)
    args = ap.parse_args()
    sourcepath, original, previous, controlpath, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("source", "original-parent", "previous-stage", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (sourcepath, original, previous, controlpath, output))
    assert not output.exists() and 31 < args.limit <= 10001
    accepted, catalogpath, frozen = parent_gate(original, sourcepath)
    old, controls = read(previous / "SUMMARY.json"), read(controlpath)
    assert old["source_sha256"] == sha(ROOT / "propose_n23_B14_full_residual.py")
    assert old["parent_report_sha256"] == sha(original / "VERIFIED.json")
    assert old["parent_pending_sha256"] == accepted["pending_sha256"]
    assert old["outcomes_sha256"] == sha(previous / "OUTCOMES.jsonl")
    assert old["actual_full_types_processed"] == accepted["pending_full_types"]
    assert controls["verified"] and controls["schema"] == "N23-B14-proposal-pending-full-supplement-selection-controls-v1"
    assert controls["proposal_source_sha256"] == sha(Path(__file__))
    assert controls["audit_source_sha256"] == sha(ROOT / "audit_n23_B14_selected_full_supplements.py")
    with (previous / "OUTCOMES.jsonl").open(encoding="ascii") as stream:
        selected = select_actual_proposal_pending(
            pending_indices(original / "PENDING.jsonl", 8277632), stream,
            accepted["pending_full_types"], old["counts"])
    assert selected
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    constants, constantshash = read(constants_path), sha(constants_path)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    for path in (Path(__file__), previous / "SUMMARY.json", previous / "OUTCOMES.jsonl",
                 ROOT / "audit_n23_B14_selected_full_supplements.py", controlpath,
                 constants_path, ROOT / "probe_collar_batches.py", HIGH / "candidate_domain.py"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    output.mkdir()
    catalog, counts = IndexedOriginal(catalogpath), Counter()
    with (output / "OUTCOMES.jsonl").open("x", encoding="ascii") as ledger:
        for index in selected:
            faces = catalog.at(index)["faces"]
            nodes, failure = make(14, 23, faces, constants, args.limit, route_weak=False)
            if nodes is None:
                outcome = {"index": index, "status": "pending", **failure}
            else:
                result = exact.verify(14, 23, faces, nodes, constants)
                assert result["verified"] and F(result["minimum_force_margin"]) > 0
                path = output / f"type-{index:08}.json.gz"
                with gzip.open(path, "xt", encoding="utf8") as stream:
                    json.dump({
                        "N": 23, "B": 14, "full_centers": 23, "index": index,
                        "faces": faces, "nodes": nodes, "parent_pending_sha256": accepted["pending_sha256"],
                        "constants_sha256": constantshash, "radius_upper": constants["radius_upper"],
                    }, stream, separators=(",", ":"))
                outcome = {"index": index, "status": "strict", "tree_sha256": sha(path),
                           "exact_result": result}
            counts[outcome["status"]] += 1
            ledger.write(json.dumps(outcome, separators=(",", ":"))+"\n")
            print("N23/B14 only actual pending complete-type deeper supplement:", index,
                  dict(counts), flush=True)
    catalog.close()
    for path, digest in frozen.items():
        assert sha(path) == digest
    publish(output / "SUMMARY.json", {
        "N": 23, "B": 14, "selected_original_proposal_pending_indices": selected,
        "counts": dict(counts), "previous_stage_report_sha256": sha(previous / "SUMMARY.json"),
        "original_parent_report_sha256": sha(original / "VERIFIED.json"),
        "parent_pending_sha256": accepted["pending_sha256"],
        "outcomes_sha256": sha(output / "OUTCOMES.jsonl"), "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)), "formal_parent_adoption_not_claimed_here": True,
        "global_optimality_proved": False,
    })
    auditor = ROOT / "audit_n23_B14_selected_full_supplements.py"
    with (output / "REPLAY-STDOUT.log").open("xb") as stdout, \
            (output / "REPLAY-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen(list(map(str, [
            sys.executable, "-u", auditor, "--source", sourcepath, "--original-parent", original,
            "--previous-stage", previous, "--stage", output, "--controls", controlpath,
            "--output", output / "REPLAYED"])),
            cwd=str(ROOT), stdout=stdout, stderr=stderr,
            creationflags=subprocess.CREATE_NO_WINDOW)
        code = process.wait()
    publish(output / "REPLAY-TERMINAL.json", {
        "actual_exit_code": code, "child_pid": process.pid, "independent_process_terminal_observed": True,
        "audit_source_sha256": sha(auditor),
    })
    assert code == 0


if __name__ == "__main__":
    main()
