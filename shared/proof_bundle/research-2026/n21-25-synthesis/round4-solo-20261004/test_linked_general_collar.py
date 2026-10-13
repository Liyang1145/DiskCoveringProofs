"""Full-set controls and exact branch acceptance for linked open-edge filling."""
from pathlib import Path
from copy import deepcopy
import argparse
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish, bind, unchanged
from stream_catalog import sha, no_duplicate_keys
from linked_general_collar_kernel import all_complete_codes, replay
from general_collar_filling_linked import internal_links_possible

assert __debug__


def derivation_gate():
    for filename, source in (
        ("general-paid-collar-source-derivation.json", "derive_general_paid_collar.py"),
        ("linked-general-paid-collar-source-derivation.json", "derive_linked_general_paid_collar.py"),
    ):
        report = read(ROOT / filename)
        assert report["verified_mechanical_derivation"] and report["source_sha256"] == sha(ROOT / source)
        for item in report["files"]:
            assert sha(ROOT / item["original"]) == item["original_sha256"]
            assert sha(ROOT / item["derived"]) == item["derived_sha256"]
            text = (ROOT / item["original"]).read_text(encoding="utf8")
            for change in item["changes"]:
                assert text.count(change["before"]) == change["occurrences"]
                text = text.replace(change["before"], change["after"])
            assert text == (ROOT / item["derived"]).read_text(encoding="utf8")
    assert read(ROOT / "general-paid-collar-source-derivation.json")["topology_provider_sha256"] == sha(ROOT / "general_collar_filling.py")
    assert read(ROOT / "linked-general-paid-collar-source-derivation.json")["link_provider_sha256"] == sha(ROOT / "general_collar_filling_linked.py")


def run(script, arguments, directory, label):
    result = subprocess.run([sys.executable, str(ROOT / script), *map(str, arguments)],
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
    derivation_gate()
    output.mkdir()
    cases, files = [], {}
    references = [
        ROOT / "n25-B14-complete-g0-simple-hole-completions-20261005-v1",
        ROOT / "n25-B16-candidate-simple-hole-completions-20261005-v1",
    ]
    for index, directory in enumerate(references):
        collar = read(directory / "INPUT-COLLAR.json")
        summary, groups = read(directory / "SUMMARY.json"), read(directory / "GROUPS.json")
        assert summary["complete_this_collar_completion_search"]
        assert summary["source_sha256"] == sha(ROOT / "complete_simple_collar.py")
        assert sha(directory / "GROUPS.json") == summary["groups_sha256"]
        expected = {tuple(r["faces"]) for r in groups["groups"]}
        actual, calls = all_complete_codes(25, collar["B"], collar["centers"], collar["faces"])
        assert actual == expected and len(actual) == groups["group_count"]
        case = output / f"case-{index}";case.mkdir()
        proposal, exact = case / "PROPOSAL.json", case / "EXACT.json"
        run("prove_linked_general_collar.py", ["--collar", directory / "INPUT-COLLAR.json",
                                              "--output", proposal, "--limit", 20000], case, "PROPOSE")
        run("replay_linked_general_collar.py", ["--collar", directory / "INPUT-COLLAR.json",
                                               "--proposal", proposal, "--output", exact], case, "REPLAY")
        accepted = read(exact)
        if collar["B"] == 16:
            assert accepted["pending_complete_leaves"] > 0 and not accepted["all_full_simple_disk_completions_strictly_paid"]
        else:
            assert accepted["all_full_simple_disk_completions_strictly_paid"]
        cases.append({"N": 25, "B": collar["B"], "full_types": len(actual), "unpaid_enumeration_states": calls,
                      "whole_complete_set_equals_frozen_simple_hole_reference": True,
                      "known_attaining_retained": collar["B"] == 16,
                      "paid_tree_nodes": accepted["nodes"], "exact_sha256": sha(exact)})
        for path in (directory / "INPUT-COLLAR.json", directory / "GROUPS.json", directory / "SUMMARY.json",
                     proposal, exact):
            bind(files, path)
        print("Linked general collar full reference:", collar["B"], len(actual), "types;", calls, "states", flush=True)
    parent = ROOT / "n25-B14-origin-force-refined-residual-20261005-v1"
    parentreport = read(parent / "VERIFIED.json")
    assert parentreport["verified"] and parentreport["residual_sha256"] == sha(parent / "RESIDUAL.jsonl")
    with (parent / "RESIDUAL.jsonl").open(encoding="ascii") as stream:
        next(stream)
        pinched = next(json.loads(line, object_pairs_hook=no_duplicate_keys)
                       for line in stream if json.loads(line)["id"] == 72263)
    case = output / "pinched-control";case.mkdir()
    collarpath = case / "INPUT-COLLAR.json"
    publish(collarpath, {"N": 25, "B": 14, "centers": pinched["centers"], "faces": pinched["faces"]})
    proposal, exact = case / "PROPOSAL.json", case / "EXACT.json"
    run("prove_linked_general_collar.py", ["--collar", collarpath, "--output", proposal, "--limit", 20000],
        case, "PROPOSE")
    run("replay_linked_general_collar.py", ["--collar", collarpath, "--proposal", proposal, "--output", exact],
        case, "REPLAY")
    accepted = read(exact)
    # This is an actual pinched example, not a claim that all such inputs close.
    assert accepted["all_full_simple_disk_completions_strictly_paid"]
    negatives = []
    payload = read(proposal)
    changed = deepcopy(payload)
    next(node for node in changed["nodes"] if node["kind"] == "SPLIT")["children"].pop()
    path = output / "DELETED-CHILD.json";publish(path, changed)
    try:
        replay(path, read(HIGH.parent / "evidence/core-reduction/constants/n25.json"))
    except (AssertionError, KeyError, IndexError):
        negatives.append("deleted-topology-child")
    else:
        raise AssertionError("general replay accepted a missing branch")
    # An internal link must be a subgraph of one simple circle.
    branch = [(1 << 14) | (1 << 15) | (1 << v) for v in (16, 17, 18)]
    assert not internal_links_possible(sorted(branch), [14])
    negatives.append("link-degree-three")
    closed = [(1 << 14) | (1 << 15) | (1 << 16),
              (1 << 14) | (1 << 16) | (1 << 17),
              (1 << 14) | (1 << 17) | (1 << 15),
              (1 << 14) | (1 << 18) | (1 << 19)]
    assert not internal_links_possible(sorted(closed), [14])
    negatives.append("closed-link-component-plus-another-component")
    limited = case / "LIMIT.json"
    run("prove_linked_general_collar.py", ["--collar", collarpath, "--output", limited, "--limit", 1],
        case, "LIMIT-PROPOSE")
    limit_result = replay(limited, read(HIGH.parent / "evidence/core-reduction/constants/n25.json"))
    assert limit_result["unsearched_frontier_nodes"] > 0 and not limit_result["all_full_simple_disk_completions_strictly_paid"]
    negatives.append("node-limit-explicitly-unpaid")
    for path in (
        Path(__file__), parent / "VERIFIED.json", parent / "RESIDUAL.jsonl", collarpath, proposal, exact,
        ROOT / "linked_general_collar_kernel.py", ROOT / "prove_linked_general_collar.py",
        ROOT / "replay_linked_general_collar.py", ROOT / "general_collar_filling.py",
        ROOT / "general_collar_filling_linked.py", ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md",
        ROOT / "general-paid-collar-source-derivation.json", ROOT / "linked-general-paid-collar-source-derivation.json",
    ):
        bind(files, path)
    unchanged(files)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "linked-general-collar-filling-controls-v1",
        "all_no_payment_complete_type_sets_equal_to_references": True,
        "cases": cases, "actual_pinched_control_parent": 72263,
        "pinched_complete_branch_cover_independently_replayed": True,
        "pinched_control_all_completions_strictly_paid": True,
        "known_attaining_candidate_not_strictly_paid": True,
        "negative_controls_rejected": negatives, "source_sha256": sha(Path(__file__)),
        "kernel_sha256": sha(ROOT / "linked_general_collar_kernel.py"),
        "provider_sha256": sha(ROOT / "general_collar_filling_linked.py"),
        "proposal_source_sha256": sha(ROOT / "prove_linked_general_collar.py"),
        "replay_source_sha256": sha(ROOT / "replay_linked_general_collar.py"),
        "source_induction_sha256": sha(ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md"),
        "files_relative_to_workspace": files, "all_pinched_collars_not_claimed": True,
        "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
