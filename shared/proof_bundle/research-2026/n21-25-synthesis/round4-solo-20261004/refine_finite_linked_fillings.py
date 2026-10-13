"""Refine a frozen finite filling stage without restarting its topology recursion."""
from pathlib import Path
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", type=Path, required=True)
    ap.add_argument("--controls", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--force-limit", type=int, default=31)
    args = ap.parse_args()
    args.stage, args.controls, args.output = (
        p.resolve() for p in (args.stage, args.controls, args.output))
    assert all(p.is_relative_to(ROOT) for p in (args.stage, args.controls, args.output))
    assert not args.output.exists() and 1 <= args.force_limit <= 1001
    stage_path = args.stage / "VERIFIED.json"
    stage, controls = read(stage_path), read(args.controls)
    assert stage["verified"] and stage["schema"] == "finite-discovery-linked-filling-payments-v1"
    assert stage["source_sha256"] == sha(ROOT / "pay_finite_discovery_fillings.py")
    assert stage["not_a_complete_competitor_family_or_union"]
    assert controls["verified"] and controls["schema"] == "linked-leaf-only-refinement-controls-v1"
    assert controls["known_exact_N25_attaining_full_type_explicitly_retained_unpaid"]
    assert controls["source_sha256"] == sha(ROOT / "test_linked_leaf_refinement.py")
    unchanged(stage["files_relative_to_workspace"])
    unchanged(controls["files_relative_to_workspace"])
    selected = [row for row in stage["outcomes"] if row["status"] == "pending"
                and row["unsearched_frontier_nodes"] == 0]
    assert selected and len(selected) <= 1024
    args.output.mkdir()
    files = {}
    for path in (Path(__file__), stage_path, args.controls, ROOT / "refine_linked_collar_leaves.py",
                 ROOT / "replay_refined_linked_leaves.py", ROOT / "linked-leaf-refinement-source-derivation.json"):
        bind(files, path)
    snapshot = []
    for row in selected:
        family = args.stage / f"sample-{row['sample']:07}"
        assert sha(family / "PROPOSAL.json") == row["proposal_sha256"]
        assert sha(family / "EXACT.json") == row["exact_sha256"]
        snapshot.append({"sample": row["sample"], "family_relative_to_round4": family.relative_to(ROOT).as_posix(),
                         "proposal_sha256": sha(family / "PROPOSAL.json"), "exact_sha256": sha(family / "EXACT.json")})
    publish(args.output / "INPUT-SNAPSHOT.json", {
        "selected_completed_pending_families": snapshot, "force_limit": args.force_limit,
        "not_a_search_or_topology_stage_restart": True, "source_sha256": sha(Path(__file__)),
        "not_a_complete_competitor_family_or_union": True, "global_optimality_proved": False,
    })
    results = []
    for number, row in enumerate(snapshot):
        family = ROOT / row["family_relative_to_round4"]
        directory = args.output / f"sample-{row['sample']:07}"
        directory.mkdir()
        proposal_path, exact_path = directory / "REFINED.json", directory / "EXACT.json"
        status = {"sample": row["sample"], "status": "unpaid"}
        for script, arguments, label in (
            ("refine_linked_collar_leaves.py",
             ["--family", family, "--output", proposal_path, "--force-limit", args.force_limit], "PROPOSE"),
            ("replay_refined_linked_leaves.py",
             ["--family", family, "--refined", proposal_path, "--output", exact_path], "REPLAY"),
        ):
            process = subprocess.run([sys.executable, str(ROOT / script), *map(str, arguments)],
                                     capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
            terminal_path = directory / (label+"-TERMINAL.json")
            publish(terminal_path, {
                "actual_exit_code": process.returncode, "independent_process_terminal_observed": True,
                "stdout": process.stdout.decode(errors="replace"), "stderr": process.stderr.decode(errors="replace"),
                "source_sha256": sha(ROOT / script),
            })
            bind(files, terminal_path)
            if process.returncode != 0:
                status["reason"] = label+" failed; family remains unpaid"
                break
        else:
            exact = read(exact_path)
            assert exact["verified"] and exact["whole_tree_fresh_exact_replayed"]
            assert exact["source_sha256"] == sha(ROOT / "replay_refined_linked_leaves.py")
            unchanged(exact["files_relative_to_workspace"])
            status.update(
                new_exact_leaf_payments=exact["new_exact_leaf_payments"],
                pending_complete_leaves=exact["pending_complete_leaves"],
                unsearched_frontier_nodes=exact["unsearched_frontier_nodes"],
                proposal_sha256=sha(proposal_path), exact_sha256=sha(exact_path))
            if exact["all_full_simple_disk_completions_strictly_paid"]:
                status["status"] = "strictly-paid-refined-complete-filling-family"
            bind(files, proposal_path);bind(files, exact_path)
        assert sha(family / "PROPOSAL.json") == row["proposal_sha256"]
        assert sha(family / "EXACT.json") == row["exact_sha256"]
        publish(directory / "STATUS.json", status)
        results.append(status)
        print("Finite linked complete-leaf refinement", number+1, "/", len(snapshot),
              "sample", row["sample"], status["status"], flush=True)
    unchanged(files)
    publish(args.output / "VERIFIED.json", {
        "verified": True, "schema": "finite-linked-filling-complete-leaf-refinement-v1",
        "N": stage["N"], "B": stage["B"], "selected_completed_pending_families": len(snapshot),
        "strictly_paid_after_refinement": sum(row["status"] != "unpaid" for row in results),
        "still_unpaid": sum(row["status"] == "unpaid" for row in results),
        "outcomes": results, "files_relative_to_workspace": files,
        "source_stage_sha256": sha(stage_path), "source_sha256": sha(Path(__file__)),
        "snapshot_sha256": sha(args.output / "INPUT-SNAPSHOT.json"),
        "only_original_FULL_PENDING_leaves_changed": True,
        "all_other_topology_states_payments_and_children_unchanged": True,
        "whole_trees_fresh_independent_exact_replayed_for_successful_results": True,
        "not_a_complete_competitor_family_or_union": True, "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
