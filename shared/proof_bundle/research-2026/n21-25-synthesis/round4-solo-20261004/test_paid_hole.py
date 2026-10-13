"""Complete source-recursion set controls, exact replay and bad tree rejection."""
from pathlib import Path
from copy import deepcopy
import argparse
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from proof_paid_hole_kernel import all_complete_codes, replay

assert __debug__


def run(script, args, directory, label):
    result = subprocess.run([sys.executable, str(ROOT / script), *map(str, args)],
                            capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    publish(directory / (label+"-TERMINAL.json"), {
        "actual_exit_code": result.returncode, "stdout": result.stdout.decode(errors="replace"),
        "stderr": result.stderr.decode(errors="replace"), "source_sha256": sha(ROOT / script),
    })
    assert result.returncode == 0, (script, result.stdout, result.stderr)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    output.mkdir()
    references = [
        ROOT / "n25-B14-complete-g0-simple-hole-completions-20261005-v1",
        ROOT / "n25-B16-candidate-simple-hole-completions-20261005-v1",
        ROOT / "n25-B14-real-residual20-collar-payments-20261005-v1/parent-0000552/COMPLETIONS",
    ]
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    cases, files = [], {}
    for index, source in enumerate(references):
        collar, groups, summary = map(read, (source / "INPUT-COLLAR.json", source / "GROUPS.json",
                                            source / "SUMMARY.json"))
        assert summary["complete_this_collar_completion_search"]
        assert summary["source_sha256"] == sha(ROOT / "complete_simple_collar.py")
        assert summary["groups_sha256"] == sha(source / "GROUPS.json")
        assert summary["input_collar_sha256"] == sha(source / "INPUT-COLLAR.json")
        expected = {tuple(r["faces"]) for r in groups["groups"]}
        codes, calls = all_complete_codes(25, collar["B"], collar["centers"], collar["faces"])
        assert codes == expected and len(expected) == groups["group_count"]
        directory = output / f"case-{index}"
        directory.mkdir()
        proposal = directory / "PROPOSAL.json"
        exact = directory / "EXACT.json"
        run("prove_paid_hole.py", ["--collar", source / "INPUT-COLLAR.json", "--output", proposal,
                                   "--limit", 20000], directory, "PROPOSE")
        run("replay_paid_hole.py", ["--collar", source / "INPUT-COLLAR.json", "--proposal", proposal,
                                    "--output", exact], directory, "REPLAY")
        accepted = read(exact)
        if collar["B"] == 16:
            assert not accepted["all_full_simple_disk_completions_strictly_paid"]
            assert accepted["pending_complete_leaves"] > 0
        else:
            assert accepted["all_full_simple_disk_completions_strictly_paid"]
        cases.append({
            "N": 25, "B": collar["B"], "source_centers": collar["centers"],
            "reference_full_types": len(expected), "full_no_payment_recursion_set_equals_frozen_reference": True,
            "no_payment_recursion_calls": calls, "paid_tree_nodes": accepted["nodes"],
            "all_simple_hole_completions_paid": accepted["all_full_simple_disk_completions_strictly_paid"],
            "known_attaining_not_strictly_excluded": collar["B"] == 16,
            "proposal_sha256": sha(proposal), "replay_sha256": sha(exact),
        })
        for path in (source / "INPUT-COLLAR.json", source / "GROUPS.json", source / "SUMMARY.json", proposal, exact):
            bind(files, path)
        print("Paid-hole full set and replay control:", collar["B"], len(expected),
              "full types;", accepted["nodes"], "tree nodes", flush=True)
    negative = []
    payload = read(output / "case-2/PROPOSAL.json")
    for label, change in (
        ("deleted-topology-child", lambda p: next(n for n in p["nodes"] if n["kind"] == "SPLIT")["children"].pop()),
        ("changed-partial-face", lambda p: next(n for n in p["nodes"] if n["kind"] == "FORCE")["state"]["faces"].pop()),
        ("bad-force-integer", lambda p: next(n for n in p["nodes"] if n["kind"] == "FORCE")["force_nodes"][0]["certificate"]["q"].__class__),
    ):
        bad = deepcopy(payload)
        if label == "bad-force-integer":
            node = next(n for n in bad["nodes"] if n["kind"] == "FORCE")
            node["force_nodes"][0]["certificate"]["q"] = 0
        else:
            change(bad)
        path = output / (label+".json");publish(path, bad)
        try:
            replay(path, constants)
        except (AssertionError, KeyError, IndexError, ZeroDivisionError):
            negative.append(label)
        else:
            raise AssertionError(("bad topology/force tree accepted", label))
    source = references[2] / "INPUT-COLLAR.json"
    proposal, exact = output / "LIMIT-PROPOSAL.json", output / "LIMIT-EXACT.json"
    run("prove_paid_hole.py", ["--collar", source, "--output", proposal, "--limit", 1], output, "LIMIT-PROPOSE")
    run("replay_paid_hole.py", ["--collar", source, "--proposal", proposal, "--output", exact], output, "LIMIT-REPLAY")
    limited = read(exact)
    assert limited["unsearched_frontier_nodes"] > 0 and not limited["all_full_simple_disk_completions_strictly_paid"]
    negative.append("node-limit-remains-explicitly-unpaid")
    for path in (Path(__file__), ROOT / "proof_paid_hole_kernel.py", ROOT / "prove_paid_hole.py",
                 ROOT / "replay_paid_hole.py", ROOT / "PROOF-PAID-HOLE-SOURCE.md",
                 ROOT / "complete_simple_collar.py", ROOT / "SIMPLE-COLLAR-COMPLETION-SOURCE.md",
                 constants_path, HIGH / "exact_graph.py", HIGH / "cross_order_strict_transfer.py"):
        bind(files, path)
    unchanged(files)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "proof-paid-simple-hole-controls-v1",
        "all_complete_no_payment_type_sets_equal_to_frozen_reference": True,
        "all_paid_force_trees_fresh_independent_process_replayed": True,
        "known_N25_attaining_full_type_not_strictly_paid": True,
        "cases": cases, "negative_controls_rejected": negative,
        "source_sha256": sha(Path(__file__)), "kernel_sha256": sha(ROOT / "proof_paid_hole_kernel.py"),
        "proposal_source_sha256": sha(ROOT / "prove_paid_hole.py"),
        "replay_source_sha256": sha(ROOT / "replay_paid_hole.py"),
        "source_induction_sha256": sha(ROOT / "PROOF-PAID-HOLE-SOURCE.md"),
        "files_relative_to_workspace": files, "complete_boundary_family_not_proved_here": True,
        "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
