"""Complete-completion-family payments for unpaid finite discovery samples.

This adapter invokes the frozen linked filling proposer and another-process
exact acceptor. Every failed start, full pending leaf, or frontier stays unpaid.
It never certifies a whole boundary family or a native search prefix.
"""
from pathlib import Path
from collections import Counter
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from group_catalog import canonical, validate
from linked_general_collar_kernel import start_states
from prove_linked_general_collar import propose

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--snapshot", type=Path, required=True)
    ap.add_argument("--receipt", type=Path, required=True)
    ap.add_argument("--replay", type=Path, required=True)
    ap.add_argument("--controls", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--limit", type=int, default=10000)
    args = ap.parse_args()
    for key in ("snapshot", "receipt", "replay", "controls", "output"):
        path = getattr(args, key).resolve()
        assert path.is_relative_to(ROOT)
        setattr(args, key, path)
    assert not args.output.exists() and 1 <= args.limit <= 100000
    snapshot, receipt, replay, controls = map(read, (
        args.snapshot, args.receipt, args.replay, args.controls))
    assert snapshot["schema"] == "incomplete-collar-discovery-v1"
    assert not snapshot["complete_necessary_outer_search"]
    assert receipt["schema"] == "individually-paid-discovery-graphs-v1"
    assert receipt["snapshot_sha256"] == replay["snapshot_sha256"] == sha(args.snapshot)
    assert replay["verified"] and replay["receipt_sha256"] == sha(args.receipt)
    assert replay["source_sha256"] == sha(ROOT / "replay_family_discovery.py")
    assert replay["exact_checker_sha256"] == sha(HIGH / "exact_graph.py")
    assert replay["no_optimizer_imported"]
    N, B = snapshot["N"], snapshot["B"]
    assert N == 25 and B in (14, 15, 16, 17)
    assert len(receipt["outcomes"]) == snapshot["weak_graph_count"] == len(snapshot["weak_graphs"])
    assert controls["verified"] and controls["schema"] == "linked-general-collar-filling-controls-v1"
    assert controls["all_no_payment_complete_type_sets_equal_to_references"]
    assert controls["pinched_complete_branch_cover_independently_replayed"]
    assert controls["known_attaining_candidate_not_strictly_paid"]
    for field, filename in (
        ("source_sha256", "test_linked_general_collar.py"),
        ("kernel_sha256", "linked_general_collar_kernel.py"),
        ("provider_sha256", "general_collar_filling_linked.py"),
        ("proposal_source_sha256", "prove_linked_general_collar.py"),
        ("replay_source_sha256", "replay_linked_general_collar.py"),
        ("source_induction_sha256", "GENERAL-COLLAR-FILLING-SOURCE.md"),
    ):
        assert controls[field] == sha(ROOT / filename)
    unchanged(controls["files_relative_to_workspace"])
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    assert receipt["constants_sha256"] == replay["constants_sha256"] == sha(constants_path)
    files = dict(snapshot.get("files_relative_to_workspace", {}))
    for path in (Path(__file__), args.snapshot, args.receipt, args.replay, args.controls,
                 constants_path, ROOT / "linked_general_collar_kernel.py",
                 ROOT / "general_collar_filling.py", ROOT / "general_collar_filling_linked.py",
                 ROOT / "prove_linked_general_collar.py", ROOT / "replay_linked_general_collar.py",
                 ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md", ROOT / "N25-COLLAR-COVER-INTERFACE.md",
                 HIGH / "exact_graph.py", HIGH / "group_catalog.py", HIGH / "probe_groups.py"):
        bind(files, path)
    unchanged(files)
    pending = []
    for index, outcome in enumerate(receipt["outcomes"]):
        assert outcome["group"] == index and outcome["status"] in ("pending", "excluded")
        row = snapshot["weak_graphs"][index]
        assert (outcome["centers"], outcome["faces"]) == (row["centers"], row["faces"])
        if outcome["status"] == "pending":
            pending.append((index, row))
    assert len(pending) == replay["totals"].get("pending", 0)
    args.output.mkdir()
    publish(args.output / "INPUT-BINDINGS.json", {
        "N": N, "B": B, "finite_pending_samples": len(pending),
        "maximum_proposed_states_per_family": args.limit, "files_relative_to_workspace": files,
        "complete_boundary_family_not_claimed": True, "global_optimality_proved": False,
    })
    counts, outcomes = Counter(), []
    for number, (index, row) in enumerate(pending):
        code, mapping = canonical(row["centers"], B, row["faces"], 1)
        assert list(code) == row["faces"] and len(mapping["centers"]) == row["centers"]
        validate(row["centers"], B, code, mapping, row["faces"])
        directory = args.output / f"sample-{index:07}"
        directory.mkdir()
        collar = {"N": N, "B": B, "centers": row["centers"], "faces": row["faces"],
                  "source_discovery_sample": index,
                  "source_snapshot_sha256": sha(args.snapshot)}
        if "selected_source_positions" in snapshot:
            collar["source_slab_position"] = snapshot["selected_source_positions"][index]
        status = {"sample": index, "centers": row["centers"], "faces": row["faces"],
                  "not_a_standalone_geometric_weak_graph_exclusion": True}
        try:
            start_states(N, B, row["centers"], row["faces"])
        except AssertionError as error:
            status.update(status="unhandled-source-topology", reason=str(error))
        else:
            collar_path = directory / "INPUT-COLLAR.json"
            publish(collar_path, collar)
            proposal = propose(collar, constants, args.limit, 1)
            proposal.update(
                source_collar_sha256=sha(collar_path), constants_sha256=sha(constants_path),
                kernel_sha256=sha(ROOT / "linked_general_collar_kernel.py"),
                source_sha256=sha(ROOT / "prove_linked_general_collar.py"),
                whole_family_payment_requires_independent_replay=True, global_optimality_proved=False)
            proposal_path, exact_path = directory / "PROPOSAL.json", directory / "EXACT.json"
            publish(proposal_path, proposal)
            result = subprocess.run([
                sys.executable, str(ROOT / "replay_linked_general_collar.py"),
                "--collar", str(collar_path), "--proposal", str(proposal_path), "--output", str(exact_path),
            ], capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
            publish(directory / "REPLAY-TERMINAL.json", {
                "actual_exit_code": result.returncode, "independent_process_terminal_observed": True,
                "stdout": result.stdout.decode(errors="replace"), "stderr": result.stderr.decode(errors="replace"),
                "source_sha256": sha(ROOT / "replay_linked_general_collar.py"),
            })
            if result.returncode != 0:
                status.update(status="failed-exact-replay")
            else:
                accepted = read(exact_path)
                assert accepted["verified"] and accepted["source_sha256"] == sha(ROOT / "replay_linked_general_collar.py")
                assert (accepted["N"], accepted["B"], accepted["collar_centers"], accepted["collar_faces"]) == (
                    N, B, row["centers"], row["faces"])
                unchanged(accepted["files_relative_to_workspace"])
                status.update(
                    status=("strictly-paid-complete-filling-family"
                            if accepted["all_full_simple_disk_completions_strictly_paid"] else "pending"),
                    exact_sha256=sha(exact_path), proposal_sha256=sha(proposal_path),
                    nodes=accepted["nodes"], pending_complete_leaves=accepted["pending_complete_leaves"],
                    unsearched_frontier_nodes=accepted["unsearched_frontier_nodes"])
                for path in (collar_path, proposal_path, exact_path, directory / "REPLAY-TERMINAL.json"):
                    bind(files, path)
        counts[status["status"]] += 1
        outcomes.append(status)
        publish(directory / "STATUS.json", status)
        print("Finite discovery completion payment", number+1, "/", len(pending),
              "sample", index, status["status"], dict(counts), flush=True)
    assert sum(counts.values()) == len(pending)
    unchanged(files)
    publish(args.output / "VERIFIED.json", {
        "verified": True, "schema": "finite-discovery-linked-filling-payments-v1",
        "N": N, "B": B, "finite_pending_samples_processed_once": len(pending),
        "strictly_paid_families": counts["strictly-paid-complete-filling-family"],
        "remaining_unpaid_families": len(pending)-counts["strictly-paid-complete-filling-family"],
        "counts": dict(counts), "outcomes": outcomes, "files_relative_to_workspace": files,
        "all_successful_trees_independent_process_replayed": True,
        "all_topological_child_lists_independently_regenerated": True,
        "source_snapshot_sha256": sha(args.snapshot), "source_sha256": sha(Path(__file__)),
        "not_a_complete_competitor_family_or_union": True, "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
