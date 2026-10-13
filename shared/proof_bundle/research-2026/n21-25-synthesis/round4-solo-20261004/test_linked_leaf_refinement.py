"""Attaining-type retention and same-topology rejection controls for linked leaves."""
from pathlib import Path
from copy import deepcopy
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import canonical_full
from n25_outer_search import read, publish, bind, unchanged

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    derivation_path = ROOT / "linked-leaf-refinement-source-derivation.json"
    derivation = read(derivation_path)
    assert derivation["verified"] and derivation["only_original_FULL_PENDING_leaves_can_change"]
    files = {}
    for record in derivation["files"]:
        source, target = ROOT / record["source"], ROOT / record["target"]
        assert sha(source) == record["source_sha256"] and sha(target) == record["target_sha256"]
        text = source.read_text(encoding="utf8")
        for before, after in record["replacements"]:
            text = text.replace(before, after)
        assert text == target.read_text(encoding="utf8")
        bind(files, source);bind(files, target)
    family = ROOT / "n25-linked-general-collar-controls-20261005-v1/case-1"
    refined_path = ROOT / "n25-linked-collar-candidate-leaf-refinement-force31-20261005-v1.json"
    exact_path = ROOT / "n25-linked-collar-candidate-leaf-refinement-force31-exact-20261005-v1.json"
    refined, exact = read(refined_path), read(exact_path)
    assert exact["verified"] and exact["whole_tree_fresh_exact_replayed"]
    assert exact["schema"] == "same-topology-linked-collar-force-refinement-exact-v1"
    assert exact["source_sha256"] == sha(ROOT / "replay_refined_linked_leaves.py")
    assert not exact["all_full_simple_disk_completions_strictly_paid"]
    assert exact["pending_complete_leaves"] > 0 and exact["unsearched_frontier_nodes"] == 0
    unchanged(exact["files_relative_to_workspace"])
    geometry_path = ROOT.parent / "evidence/n25-algebraic-upper-round2/geometry.json"
    geometry = read(geometry_path)
    known = canonical_full(25, 16, sorted(sum(1 << v for v in face) for face in geometry["faces"]))
    retained = [index for index, node in enumerate(refined["nodes"])
                if node["kind"] == "FULL_PENDING" and node["state"]["next"] == 25
                and canonical_full(25, 16, node["state"]["faces"]) == known]
    assert retained, "Known exact-rstar attaining full graph must remain explicitly unpaid"
    output.mkdir()
    rejected = []
    for label in ("deleted-topology-child", "changed-complete-leaf-state",
                  "changed-original-paid-node", "false-changed-leaf-list"):
        bad = deepcopy(refined)
        if label == "deleted-topology-child":
            node = next(n for n in bad["nodes"] if n["kind"] == "SPLIT")
            node["children"].pop()
        elif label == "changed-complete-leaf-state":
            bad["nodes"][retained[0]]["state"]["faces"].pop()
        elif label == "changed-original-paid-node":
            old = read(family / "PROPOSAL.json")
            index = next(i for i, node in enumerate(old["nodes"]) if node["kind"] == "ANGLE")
            bad["nodes"][index]["state"]["faces"].pop()
        else:
            assert bad["refined_leaf_indices"]
            bad["refined_leaf_indices"].pop()
        proposal_path, rejected_path = output / (label+".json"), output / (label+"-exact.json")
        publish(proposal_path, bad)
        process = subprocess.run([
            sys.executable, str(ROOT / "replay_refined_linked_leaves.py"),
            "--family", str(family), "--refined", str(proposal_path), "--output", str(rejected_path),
        ], capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        assert process.returncode != 0 and not rejected_path.exists(), label
        publish(output / (label+"-TERMINAL.json"), {
            "actual_exit_code": process.returncode,
            "stdout": process.stdout.decode(errors="replace"), "stderr": process.stderr.decode(errors="replace"),
        })
        rejected.append(label)
    for path in (Path(__file__), derivation_path, refined_path, exact_path, geometry_path,
                 family / "PROPOSAL.json", family / "EXACT.json"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "linked-leaf-only-refinement-controls-v1",
        "known_exact_N25_attaining_full_type_explicitly_retained_unpaid": True,
        "known_attaining_pending_node_indices": retained,
        "candidate_newly_paid_leaves": exact["new_exact_leaf_payments"],
        "only_original_FULL_PENDING_leaves_changed": True,
        "negative_controls_rejected": rejected, "files_relative_to_workspace": files,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("Linked leaf-only refinement controls PASS:", len(retained),
          "explicit attaining leaves retained;", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
