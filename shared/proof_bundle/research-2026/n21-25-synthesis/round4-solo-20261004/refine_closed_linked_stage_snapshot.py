"""Freeze and refine completed immutable linked families while a larger stage proceeds.

This is a one-shot snapshot, not a monitor, topology restart, or full-stage
acceptance. Every selected source family already has an observed successful
independent exact replay and a final per-family status file.
"""
from pathlib import Path
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from group_catalog import canonical, validate

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", type=Path, required=True)
    ap.add_argument("--snapshot", type=Path, required=True)
    ap.add_argument("--receipt", type=Path, required=True)
    ap.add_argument("--controls", type=Path, required=True)
    ap.add_argument("--already-refined", type=Path, action="append", default=[])
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--count", type=int, default=256)
    ap.add_argument("--force-limit", type=int, default=31)
    args = ap.parse_args()
    for key in ("stage", "snapshot", "receipt", "controls", "output"):
        path = getattr(args, key).resolve()
        assert path.is_relative_to(ROOT)
        setattr(args, key, path)
    assert not args.output.exists() and 1 <= args.count <= 1024 and 1 <= args.force_limit <= 1001
    input_path = args.stage / "INPUT-BINDINGS.json"
    stage_inputs, snapshot, receipt, controls = map(read, (
        input_path, args.snapshot, args.receipt, args.controls))
    assert stage_inputs["complete_boundary_family_not_claimed"]
    source_relative = (ROOT / "pay_finite_discovery_fillings.py").relative_to(ROOT.parents[2]).as_posix()
    assert stage_inputs["files_relative_to_workspace"][source_relative] == sha(ROOT / "pay_finite_discovery_fillings.py")
    unchanged(stage_inputs["files_relative_to_workspace"])
    assert snapshot["schema"] == "incomplete-collar-discovery-v1"
    assert snapshot["not_a_complete_competitor_family_or_union"]
    assert receipt["snapshot_sha256"] == sha(args.snapshot)
    assert receipt["schema"] == "individually-paid-discovery-graphs-v1"
    assert len(receipt["outcomes"]) == snapshot["weak_graph_count"]
    assert controls["verified"] and controls["schema"] == "linked-leaf-only-refinement-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_linked_leaf_refinement.py")
    assert controls["known_exact_N25_attaining_full_type_explicitly_retained_unpaid"]
    unchanged(controls["files_relative_to_workspace"])
    N, B = snapshot["N"], snapshot["B"]
    assert (stage_inputs["N"], stage_inputs["B"]) == (N, B)
    already = set()
    for previous in args.already_refined:
        previous = previous.resolve()
        assert previous.is_relative_to(ROOT)
        old_snapshot = read(previous / "INPUT-SNAPSHOT.json")
        assert old_snapshot["source_discovery_snapshot_sha256"] == sha(args.snapshot)
        assert old_snapshot["force_limit"] >= args.force_limit
        already.update(row["sample"] for row in old_snapshot["selected_completed_pending_families"])
    selected = []
    for status_path in sorted(args.stage.glob("sample-*/STATUS.json")):
        try:
            status = read(status_path)
        except (ValueError, OSError):
            # Only a per-family status that has completely finished publishing
            # is eligible; the current writer's last file cannot be used.
            continue
        sample = status["sample"]
        if sample in already or status["status"] != "pending" or status["unsearched_frontier_nodes"] != 0:
            continue
        family = status_path.parent
        exact_path, proof_path, terminal_path = (
            family / name for name in ("EXACT.json", "PROPOSAL.json", "REPLAY-TERMINAL.json"))
        exact, terminal = read(exact_path), read(terminal_path)
        assert exact["verified"] and exact["schema"] == "proof-paid-linked-general-collar-independent-replay-v1"
        assert exact["source_sha256"] == sha(ROOT / "replay_linked_general_collar.py")
        assert exact["pending_complete_leaves"] > 0 and exact["unsearched_frontier_nodes"] == 0
        assert terminal["actual_exit_code"] == 0 and terminal["independent_process_terminal_observed"]
        assert terminal["source_sha256"] == sha(ROOT / "replay_linked_general_collar.py")
        assert status["exact_sha256"] == sha(exact_path) and status["proposal_sha256"] == sha(proof_path)
        unchanged(exact["files_relative_to_workspace"])
        graph = snapshot["weak_graphs"][sample]
        outcome = receipt["outcomes"][sample]
        assert outcome["group"] == sample and outcome["status"] == "pending"
        assert (status["centers"], status["faces"]) == (graph["centers"], graph["faces"])
        assert (exact["N"], exact["B"], exact["collar_centers"], exact["collar_faces"]) == (
            N, B, graph["centers"], graph["faces"])
        code, mapping = canonical(graph["centers"], B, graph["faces"], 1)
        assert list(code) == graph["faces"] and len(mapping["centers"]) == graph["centers"]
        validate(graph["centers"], B, code, mapping, graph["faces"])
        selected.append({
            "sample": sample, "family_relative_to_round4": family.relative_to(ROOT).as_posix(),
            "status_sha256": sha(status_path), "proposal_sha256": sha(proof_path), "exact_sha256": sha(exact_path),
            "successful_replay_terminal_sha256": sha(terminal_path),
        })
        if len(selected) == args.count:
            break
    assert selected
    args.output.mkdir()
    files = {}
    for path in (Path(__file__), input_path, args.snapshot, args.receipt, args.controls,
                 ROOT / "refine_linked_collar_leaves.py", ROOT / "replay_refined_linked_leaves.py",
                 ROOT / "linked-leaf-refinement-source-derivation.json"):
        bind(files, path)
    publish(args.output / "INPUT-SNAPSHOT.json", {
        "selected_completed_pending_families": selected,
        "source_discovery_snapshot_sha256": sha(args.snapshot),
        "source_stage_input_bindings_sha256": sha(input_path), "force_limit": args.force_limit,
        "no_live_family_source_file_changed": True, "not_a_stage_or_topology_restart": True,
        "not_the_complete_parent_residual_pass": True, "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False,
    })
    results = []
    for number, row in enumerate(selected):
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
                status["reason"] = label+" failed; family stays unpaid"
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
        assert sha(family / "STATUS.json") == row["status_sha256"]
        assert sha(family / "PROPOSAL.json") == row["proposal_sha256"]
        assert sha(family / "EXACT.json") == row["exact_sha256"]
        assert sha(family / "REPLAY-TERMINAL.json") == row["successful_replay_terminal_sha256"]
        publish(directory / "STATUS.json", status)
        results.append(status)
        print("Frozen completed linked family refined:", number+1, "/", len(selected),
              "sample", row["sample"], status["status"], flush=True)
    unchanged(files)
    publish(args.output / "VERIFIED.json", {
        "verified": True, "schema": "frozen-completed-linked-family-leaf-refinement-v1",
        "N": N, "B": B, "selected_completed_pending_families": len(selected),
        "strictly_paid_after_refinement": sum(row["status"] != "unpaid" for row in results),
        "still_unpaid": sum(row["status"] == "unpaid" for row in results), "outcomes": results,
        "source_discovery_snapshot_sha256": sha(args.snapshot),
        "snapshot_sha256": sha(args.output / "INPUT-SNAPSHOT.json"),
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "all_successful_refined_trees_whole_replayed_in_independent_process": True,
        "only_original_FULL_PENDING_leaves_changed": True,
        "not_the_complete_parent_residual_pass": True, "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
