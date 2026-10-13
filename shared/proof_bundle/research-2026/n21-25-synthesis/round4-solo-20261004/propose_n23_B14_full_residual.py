"""Retain all30 actual source faces, then automatically invoke independent replay."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
import argparse
import gzip
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from audit_n23_B14_full_residual import parent_gate
from audit_n23_B14_pending_outer import IndexedOriginal
from audit_n23_B15_effective_outer_payment import pending_indices
from probe_collar_batches import make
import exact_graph as exact

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("source", "parent", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--limit", type=int, default=31)
    args = ap.parse_args()
    sourcepath, parent, controlpath, output = (
        getattr(args, name).resolve() for name in ("source", "parent", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (sourcepath, parent, controlpath, output))
    assert not output.exists() and 1 <= args.limit <= 5001
    accepted, catalogpath, frozen = parent_gate(parent, sourcepath)
    controls = read(controlpath)
    assert controls["verified"] and controls["schema"] == "N23-B14-actual-full-residual-type-controls-v1"
    assert controls["audit_source_sha256"] == sha(ROOT / "audit_n23_B14_full_residual.py")
    assert controls["proposal_source_sha256"] == sha(Path(__file__))
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    constants, constantshash = read(constants_path), sha(constants_path)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    for path in (Path(__file__), controlpath, constants_path, ROOT / "audit_n23_B14_full_residual.py",
                 ROOT / "audit_n23_B14_pending_outer.py", ROOT / "probe_collar_batches.py",
                 HIGH / "candidate_domain.py", HIGH / "exact_graph.py"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "N": 23, "B": 14, "parent_report_sha256": sha(parent / "VERIFIED.json"),
        "parent_pending_sha256": accepted["pending_sha256"],
        "actual_current_full_types": accepted["pending_full_types"],
        "all_actual_complete_faces_retained_not_outer_only": True,
        "no_B15_attaining_core_or_other_order_constants_transported_to_B14": True,
        "force_limit": args.limit, "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    catalog = IndexedOriginal(catalogpath)
    counts, started = Counter(), time.monotonic()
    with (output / "OUTCOMES.jsonl").open("x", encoding="ascii") as ledger:
        for index in pending_indices(parent / "PENDING.jsonl", 8277632):
            original = catalog.at(index)
            faces = original["faces"]
            assert len(faces) == 30
            nodes, failure = make(14, 23, faces, constants, args.limit, route_weak=False)
            if nodes is None:
                outcome = {"index": index, "status": "pending", **failure}
            else:
                result = exact.verify(14, 23, faces, nodes, constants)
                assert result["verified"] and F(result["minimum_force_margin"]) > 0
                treepath = output / f"type-{index:08}.json.gz"
                with gzip.open(treepath, "xt", encoding="utf8") as stream:
                    json.dump({
                        "N": 23, "B": 14, "full_centers": 23, "index": index,
                        "faces": faces, "nodes": nodes,
                        "parent_pending_sha256": accepted["pending_sha256"],
                        "constants_sha256": constantshash, "radius_upper": constants["radius_upper"],
                    }, stream, separators=(",", ":"))
                outcome = {"index": index, "status": "strict", "tree_sha256": sha(treepath),
                           "exact_result": result}
            counts[outcome["status"]] += 1
            ledger.write(json.dumps(outcome, separators=(",", ":"))+"\n")
            if sum(counts.values()) % 100 == 0:
                ledger.flush()
                print("N23/B14 complete actual type proposals", sum(counts.values()),
                      "/", accepted["pending_full_types"], dict(counts),
                      "seconds", round(time.monotonic()-started, 1), flush=True)
    catalog.close()
    assert sum(counts.values()) == accepted["pending_full_types"]
    for path, digest in frozen.items():
        assert sha(path) == digest
    publish(output / "SUMMARY.json", {
        "N": 23, "B": 14, "actual_full_types_processed": sum(counts.values()), "counts": dict(counts),
        "parent_report_sha256": sha(parent / "VERIFIED.json"),
        "parent_pending_sha256": accepted["pending_sha256"],
        "all_actual_complete_faces_retained_not_outer_only": True,
        "outcomes_sha256": sha(output / "OUTCOMES.jsonl"),
        "input_bindings_sha256": sha(output / "INPUT-BINDINGS.json"),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "independent_actual_source_and_math_payment_acceptance_still_required": True,
        "global_optimality_proved": False,
    })
    auditor = ROOT / "audit_n23_B14_full_residual.py"
    with (output / "AUDIT-STDOUT.log").open("xb") as stdout, \
            (output / "AUDIT-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen(list(map(str, [
            sys.executable, "-u", auditor, "--source", sourcepath, "--parent", parent,
            "--stage", output, "--controls", controlpath, "--output", output / "ACCEPTED"])),
            cwd=str(ROOT), stdout=stdout, stderr=stderr,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / "AUDIT-TERMINAL.json", {
        "actual_exit_code": code, "child_pid": process.pid,
        "independent_process_terminal_observed": True, "audit_source_sha256": sha(auditor),
    })
    assert code == 0
    print("N23/B14 complete actual-type proposal and independent acceptance ended", flush=True)


if __name__ == "__main__":
    main()
