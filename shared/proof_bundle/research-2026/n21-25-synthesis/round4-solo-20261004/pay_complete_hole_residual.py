"""Sequential exact branch payments over every remaining complete B14 residual."""
from pathlib import Path
from collections import Counter
import argparse
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish, bind, unchanged
from complete_simple_collar import simple_holes
from proof_paid_hole_kernel import replay
from prove_paid_hole import propose

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--parent", type=Path, required=True)
    ap.add_argument("--controls", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--limit", type=int, default=20000)
    args = ap.parse_args()
    parent, output, controlspath = (p.resolve() for p in (args.parent, args.output, args.controls))
    assert output.is_relative_to(ROOT) and not output.exists()
    assert 1 <= args.limit <= 100000
    controls = read(controlspath)
    assert controls["verified"] and controls["schema"] == "proof-paid-simple-hole-controls-v1"
    for field, name in (("source_sha256", "test_paid_hole.py"), ("kernel_sha256", "proof_paid_hole_kernel.py"),
                        ("proposal_source_sha256", "prove_paid_hole.py"), ("replay_source_sha256", "replay_paid_hole.py"),
                        ("source_induction_sha256", "PROOF-PAID-HOLE-SOURCE.md")):
        assert controls[field] == sha(ROOT / name)
    assert controls["all_complete_no_payment_type_sets_equal_to_frozen_reference"]
    assert controls["all_paid_force_trees_fresh_independent_process_replayed"]
    assert controls["known_N25_attaining_full_type_not_strictly_paid"]
    assert [r["reference_full_types"] for r in controls["cases"]] == [217, 91, 9773]
    assert set(controls["negative_controls_rejected"]) == {
        "deleted-topology-child", "changed-partial-face", "bad-force-integer", "node-limit-remains-explicitly-unpaid"}
    unchanged(controls["files_relative_to_workspace"])
    reportpath, sourcepath = parent / "VERIFIED.json", parent / "RESIDUAL.jsonl"
    report = read(reportpath)
    assert report["verified"] and report["schema"] == "complete-origin-residual-exact-force-refinement-v1"
    assert report["source_sha256"] == sha(ROOT / "pay_origin_refined_force.py")
    assert report["every_parent_residual_row_compared_with_complete_catalog_and_identity_map"]
    assert report["every_accepted_tree_fresh_standard_library_replayed"]
    assert sha(sourcepath) == report["residual_sha256"]
    unchanged(report["files_relative_to_workspace"])
    N, B = report["N"], report["B"]
    assert N == 25 and B in (14, 15, 16, 17)
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    files = {}
    for path in (Path(__file__), reportpath, sourcepath, controlspath, constants_path,
                 ROOT / "proof_paid_hole_kernel.py", ROOT / "prove_paid_hole.py", ROOT / "replay_paid_hole.py",
                 ROOT / "PROOF-PAID-HOLE-SOURCE.md", ROOT / "complete_simple_collar.py",
                 ROOT / "SIMPLE-COLLAR-COMPLETION-SOURCE.md", ROOT / "CLOSED-BOUNDARY-FAN-TRANSFER.md",
                 HIGH / "exact_graph.py", HIGH.parent / "round2-grouped/partial_force_exact.py"):
        bind(files, path)
    unchanged(files)
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "N": N, "B": B, "parent_residual_weak_graphs": report["remaining_weak_graphs"],
        "source_catalog_sha256": report["parent_catalog_sha256"],
        "source_residual_sha256": report["residual_sha256"],
        "maximum_proposed_states_per_family": args.limit,
        "files_relative_to_workspace": files, "whole_boundary_family_not_claimed": True,
        "global_optimality_proved": False,
    })
    counts, processed, last = Counter(), 0, -1
    ledgerpath, residualpath = output / "PAYMENTS.jsonl", output / "RESIDUAL.jsonl"
    with sourcepath.open(encoding="ascii") as source, ledgerpath.open("x", encoding="ascii") as ledger, \
            residualpath.open("x", encoding="ascii") as unresolved:
        header = json.loads(next(source), object_pairs_hook=no_duplicate_keys)
        assert header["schema"] == "complete-collar-origin-and-exact-force-residual-v1"
        assert header["source_catalog_sha256"] == report["parent_catalog_sha256"]
        unresolved.write(json.dumps({
            "schema": "complete-collar-exact-paid-hole-residual-v1", "N": N, "B": B,
            "source_catalog_sha256": report["parent_catalog_sha256"],
            "parent_exact_refinement_report_sha256": sha(reportpath),
            "members_are_weak_graphs_not_full_types": True,
        }, separators=(",", ":"))+"\n")
        for line in source:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            gid, centers, outer = row["id"], row["centers"], row["faces"]
            assert last < gid and row["members"] == 1
            last = gid
            directory = output / f"parent-{gid:07}"
            directory.mkdir()
            status = {"parent_group": gid, "not_a_standalone_geometric_weak_graph_exclusion": True}
            try:
                holes = simple_holes(centers, B, outer)
            except AssertionError as error:
                status.update(status="unhandled", reason=str(error))
                counts["unhandled"] += 1
            else:
                collarpath = directory / "INPUT-COLLAR.json"
                collar = {"N": N, "B": B, "centers": centers, "faces": outer, "holes": holes,
                          "source_parent_group": gid}
                publish(collarpath, collar)
                payload = propose(collar, constants, args.limit, 1)
                proposalpath = directory / "PROPOSAL.json"
                payload.update(source_collar_sha256=sha(collarpath), constants_sha256=sha(constants_path),
                               kernel_sha256=sha(ROOT / "proof_paid_hole_kernel.py"),
                               source_sha256=sha(ROOT / "prove_paid_hole.py"),
                               whole_family_payment_requires_independent_replay=True,
                               global_optimality_proved=False)
                publish(proposalpath, payload)
                replaypath = directory / "EXACT.json"
                result = subprocess.run([
                    sys.executable, str(ROOT / "replay_paid_hole.py"), "--collar", str(collarpath),
                    "--proposal", str(proposalpath), "--output", str(replaypath),
                ], capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
                publish(directory / "REPLAY-TERMINAL.json", {
                    "actual_exit_code": result.returncode, "independent_process_terminal_observed": True,
                    "stdout": result.stdout.decode(errors="replace"), "stderr": result.stderr.decode(errors="replace"),
                    "source_sha256": sha(ROOT / "replay_paid_hole.py"),
                })
                if result.returncode == 0:
                    accepted = read(replaypath)
                    assert accepted["verified"] and accepted["source_sha256"] == sha(ROOT / "replay_paid_hole.py")
                    assert (accepted["N"], accepted["B"], accepted["collar_centers"], accepted["collar_faces"]) == (
                        N, B, centers, outer)
                    unchanged(accepted["files_relative_to_workspace"])
                    if accepted["all_full_simple_disk_completions_strictly_paid"]:
                        counts["strictly_paid_simple_hole_families"] += 1
                        status.update(status="strictly-paid-complete-simple-hole-family",
                                      proposal_sha256=sha(proposalpath), exact_sha256=sha(replaypath),
                                      branch_nodes=accepted["nodes"])
                        ledger.write(json.dumps(status, separators=(",", ":"))+"\n")
                    else:
                        counts["pending_simple_hole_families"] += 1
                        status.update(status="pending", exact_sha256=sha(replaypath),
                                      pending_complete_leaves=accepted["pending_complete_leaves"],
                                      unsearched_frontier_nodes=accepted["unsearched_frontier_nodes"])
                else:
                    counts["failed_exact_replay"] += 1
                    status.update(status="failed-exact-replay")
            publish(directory / "STATUS.json", status)
            if status["status"] != "strictly-paid-complete-simple-hole-family":
                unresolved.write(json.dumps(row, separators=(",", ":"))+"\n")
            processed += 1
            ledger.flush();unresolved.flush()
            if processed % 10 == 0:
                print("Complete residual paid-hole progress:", processed, "/", report["remaining_weak_graphs"],
                      dict(counts), flush=True)
    assert processed == report["remaining_weak_graphs"] == sum(counts.values())
    unchanged(files)
    remaining = processed-counts["strictly_paid_simple_hole_families"]
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-residual-proof-paid-simple-hole-refinement-v1", "N": N, "B": B,
        "every_complete_parent_residual_row_processed_once": True, "parent_residual_weak_graphs": processed,
        "counts": dict(counts), "remaining_weak_graphs": remaining,
        "all_exact_force_leaves_independent_process_replayed": True,
        "all_topological_child_lists_independently_regenerated": True,
        "parent_report_sha256": sha(reportpath), "payments_sha256": sha(ledgerpath),
        "residual_sha256": sha(residualpath), "files_relative_to_workspace": files,
        "source_sha256": sha(Path(__file__)), "full_boundary_family_completion_not_claimed": True,
        "global_optimality_proved": False,
    })
    print("Complete paid-hole residual pass accepted:", dict(counts), "; remaining:", remaining, flush=True)


if __name__ == "__main__":
    main()
