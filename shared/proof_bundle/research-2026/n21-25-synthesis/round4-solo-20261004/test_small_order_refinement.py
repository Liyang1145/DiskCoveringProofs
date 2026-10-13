"""Real source-bound pending family and topology/source/order refusal controls."""
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
from refine_small_order_family import original_gate, refinement_shape

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--family", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    family, output = args.family.resolve(), args.output.resolve()
    assert family.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    old, accepted, _, _ = original_gate(family)
    output.mkdir()
    proof, exact = output / "REFINED.json", output / "EXACT.json"
    for label, arguments in (
        ("PROPOSE", ["--family", family, "--output", proof, "--force-limit", 511]),
        ("REPLAY", ["--audit", "--family", family, "--refined", proof, "--output", exact])):
        with (output / (label+"-STDOUT.log")).open("xb") as stdout, \
                (output / (label+"-STDERR.log")).open("xb") as stderr:
            process = subprocess.Popen(list(map(str, [
                sys.executable, "-u", ROOT / "refine_small_order_family.py", *arguments])),
                cwd=str(ROOT), stdout=stdout, stderr=stderr,
                env=dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1"),
                creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
            code = process.wait()
        publish(output / (label+"-TERMINAL.json"), {
            "pid": process.pid, "actual_exit_code": code,
            "actual_child_terminal_observed": True})
        assert code == 0, label
    new, result = read(proof), read(exact)
    assert result["verified"] and result["whole_completion_family_strictly_closed"]
    assert result["new_exact_leaf_payments"] > 0
    refused = []
    def reject(name, value):
        try:
            refinement_shape(old, value)
        except (AssertionError, KeyError):
            refused.append(name)
        else:
            raise AssertionError("illegal old branch change accepted: "+name)
    for field, value in (
        ("N", 25), ("B", 15), ("cap8", 4058615), ("radius_upper", "1/4"),
        ("constants_sha256", "0"*64), ("roots", old["roots"]+[old["roots"][0]]),
        ("collar_faces", old["collar_faces"][:-1]), ("source_collar_sha256", "0"*64)):
        bad = deepcopy(new)
        bad[field] = value
        reject(field, bad)
    bad = deepcopy(new)
    bad["nodes"].append(deepcopy(bad["nodes"][0]))
    reject("extra-topology-node", bad)
    bad = deepcopy(new)
    next(node for node in bad["nodes"] if node["kind"] == "SPLIT")["children"].pop()
    reject("old-child-deletion", bad)
    bad = deepcopy(new)
    index = bad["refined_leaf_indices"][0]
    bad["nodes"][index]["state"]["next"] -= 1
    reject("different-complete-leaf-state", bad)
    bad = deepcopy(new)
    bad["refined_leaf_indices"].pop()
    reject("missing-changed-leaf-accounting", bad)
    for path, digest in accepted["frozen_files"].items():
        assert sha(path) == digest
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "small-order-real-full-pending-leaf-refinement-controls-v1",
        "actual_original_pending_family": str(family),
        "own_order_real_full_family_strict_positive_separate_process_replayed": True,
        "wrong_order_constants_source_state_and_topology_refusals": refused,
        "old_already_paid_branches_and_topology_retained_unchanged": True,
        "not_a_complete_boundary_source_payment": True,
        "source_sha256": sha(Path(__file__)),
        "refinement_source_sha256": sha(ROOT / "refine_small_order_family.py"),
        "positive_exact_report_sha256": sha(exact), "global_optimality_proved": False})
    print("Own-order real full-pending leaf refinement controls accepted:", len(refused),
          "refusals; actual whole family closed", flush=True)


if __name__ == "__main__":
    main()
