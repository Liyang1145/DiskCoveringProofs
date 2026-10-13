"""Refine a frozen snapshot of completed unpaid families, not a monitor or restart."""
from pathlib import Path
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from n25_outer_search import read, publish, unchanged
from stream_catalog import sha

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--already-paid", type=Path, action="append", default=[])
    ap.add_argument("--count", type=int, default=100)
    ap.add_argument("--force-limit", type=int, default=31)
    args = ap.parse_args()
    stage, output = args.stage.resolve(), args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists() and 1 <= args.count <= 1000
    knownpath = ROOT / "n25-paid-hole-refinement-candidate-control-20261005-v1.json"
    known = read(knownpath)
    assert known["verified"] and known["known_exact_N25_attaining_full_type_explicitly_in_unpaid_leaves"]
    assert known["refined_proposal_sha256"] == sha(ROOT / "n25-paid-hole-candidate-force31-control-20261005-v1.json")
    assert known["exact_report_sha256"] == sha(ROOT / "n25-paid-hole-candidate-force31-control-exact-20261005-v1.json")
    paid_faces = set()
    for path in args.already_paid:
        accepted = read(path)
        assert accepted["verified"] and accepted["all_full_simple_disk_completions_strictly_paid"]
        assert accepted["source_sha256"] == sha(ROOT / "replay_refined_hole_leaves.py")
        unchanged(accepted["files_relative_to_workspace"])
        paid_faces.add(tuple(accepted["collar_faces"]))
    selected = []
    for path in sorted(stage.glob("parent-*/STATUS.json")):
        status = read(path)
        if status["status"] != "pending" or status.get("unsearched_frontier_nodes", 0):
            continue
        exactpath = path.parent / "EXACT.json"
        exact = read(exactpath)
        assert exact["verified"] and exact["pending_complete_leaves"] > 0
        if tuple(exact["collar_faces"]) in paid_faces:
            continue
        selected.append({"parent_group": status["parent_group"], "directory": path.parent,
                         "status_sha256": sha(path), "exact_sha256": sha(exactpath),
                         "proposal_sha256": sha(path.parent / "PROPOSAL.json")})
        if len(selected) == args.count:
            break
    assert selected
    output.mkdir()
    publish(output / "INPUT-SNAPSHOT.json", {
        "selected_completed_pending_families": [{**row, "directory": row["directory"].relative_to(ROOT).as_posix()}
                                               for row in selected],
        "not_a_live_stage_restart": True, "not_the_complete_parent_residual_pass": True,
        "force_limit": args.force_limit, "source_sha256": sha(Path(__file__)),
        "known_attaining_control_sha256": sha(knownpath), "global_optimality_proved": False,
    })
    results = []
    for row in selected:
        gid, family = row["parent_group"], row["directory"]
        directory = output / f"parent-{gid:07}";directory.mkdir()
        proposal, exactpath = directory / "REFINED.json", directory / "EXACT.json"
        status = {"parent_group": gid, "status": "unpaid"}
        for script, arguments, label in (
            ("refine_paid_hole_leaves.py", ["--family", family, "--output", proposal,
                                           "--force-limit", args.force_limit], "PROPOSE"),
            ("replay_refined_hole_leaves.py", ["--family", family, "--refined", proposal,
                                              "--output", exactpath], "REPLAY"),
        ):
            process = subprocess.run([sys.executable, str(ROOT / script), *map(str, arguments)],
                                     capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
            publish(directory / (label+"-TERMINAL.json"), {
                "actual_exit_code": process.returncode, "independent_process_terminal_observed": True,
                "stdout": process.stdout.decode(errors="replace"), "stderr": process.stderr.decode(errors="replace"),
                "source_sha256": sha(ROOT / script),
            })
            if process.returncode != 0:
                status["reason"] = label+" process failed; not paid"
                break
        else:
            accepted = read(exactpath)
            assert accepted["verified"] and accepted["whole_tree_fresh_exact_replayed"]
            assert accepted["source_sha256"] == sha(ROOT / "replay_refined_hole_leaves.py")
            unchanged(accepted["files_relative_to_workspace"])
            status.update(exact_sha256=sha(exactpath), remaining_complete_leaves=accepted["pending_complete_leaves"])
            if accepted["all_full_simple_disk_completions_strictly_paid"]:
                status["status"] = "strictly-paid-refined-simple-hole-family"
        assert sha(family / "STATUS.json") == row["status_sha256"]
        assert sha(family / "EXACT.json") == row["exact_sha256"]
        assert sha(family / "PROPOSAL.json") == row["proposal_sha256"]
        publish(directory / "STATUS.json", status)
        results.append(status)
        print("Completed pending family refined:", gid, status["status"], flush=True)
    publish(output / "SUMMARY.json", {
        "verified": True, "selected_completed_pending_families": len(selected),
        "strictly_paid_after_refinement": sum(r["status"] == "strictly-paid-refined-simple-hole-family" for r in results),
        "still_unpaid": sum(r["status"] == "unpaid" for r in results), "results": results,
        "source_sha256": sha(Path(__file__)), "snapshot_sha256": sha(output / "INPUT-SNAPSHOT.json"),
        "all_other_parent_rows_not_paid_here": True, "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
