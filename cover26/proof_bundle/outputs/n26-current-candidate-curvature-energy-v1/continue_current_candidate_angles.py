"""Frozen semantic continuation of the already continued candidate angle tree."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from audit_prefix_partition import linux
from n26_force import load_trig
import n26_current_continued_leaf_source as current
import verify_continued_leaf_angles as continuation


leaf = current.original.leaf
INPUTS = ("source", "old-leaf", "correlated", "sharp", "historical",
          "pinning-basis", "stress", "local", "transport", "pinning", "caps")


def read(path):
    return json.loads(leaf.local_path(str(path)).read_text(encoding="utf-8"))


def publish_or_match(path, value):
    if path.exists():
        if read(path) != value:
            raise ValueError("published continued candidate data changed: " + path.name)
    else:
        path.write_text(json.dumps(value, separators=(",", ":")) + "\n", encoding="utf-8")


def input_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != "N26-current-candidate-continuation-bindings-v1":
        raise ValueError("wrong current candidate continuation bindings")
    for name, digest in manifest["copied_files"].items():
        if leaf.sha(folder / name) != digest:
            raise ValueError("sealed current candidate continuation changed: " + name)
    paths = [leaf.local_path(manifest["sources"][key]) for key in INPUTS]
    values = current.input_gate(*paths)
    if (leaf.sha(paths[0] / "VERIFIED.json") != manifest["source_acceptance_sha256"]
            or read(folder / "SOURCE-ACCEPTANCE.json") != values["accepted"]
            or read(folder / "SOURCE-CERTIFICATE.json") != values["source"]):
        raise ValueError("current candidate continuation substituted its source")
    proposal = read(folder / "PROPOSAL.json")
    if (proposal["schema"] != "N26-unaccepted-current-candidate-leaf-continuation-v1"
            or proposal["verified"] is not False):
        raise ValueError("wrong current candidate discovery format")
    continuation.proposal_gate(values["source"], paths[0], proposal)
    for module in (current, continuation, current.original, leaf):
        name = Path(module.__file__).name
        if leaf.sha(module.__file__) != manifest["copied_files"][name]:
            raise ValueError("continuation imported different sealed arithmetic")
    return manifest, paths, values, proposal


def verify(folder, report_path):
    if report_path.exists():
        raise FileExistsError(report_path)
    manifest, paths, values, proposal = input_gate(folder)
    inventory = {linux(path): leaf.sha(path) for path in values["inventory"]}
    arcs = load_trig(paths[0])[0]
    nodes, result, pending, ledger, empty, local = continuation.replay_and_close(values, proposal, arcs)
    leaf.lineage_gate(values["source"]["nodes"], nodes)
    negatives = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid current continuation accepted: " + label)

    for kind in (leaf.HULL_LOCAL, "SHARP_CORRELATED_FORCE", "SHARP_FORCE", "SPLIT"):
        bad = deepcopy(nodes)
        index = next(i for i, node in enumerate(values["source"]["nodes"]) if node["kind"] == kind)
        bad[index] = {"kind": "OPEN"}
        reject("old-" + kind + "-erased",
               lambda bad=bad: leaf.lineage_gate(values["source"]["nodes"], bad))
    bad = deepcopy(nodes)
    split = next(node for node in bad[len(values["source"]["nodes"]):] if node["kind"] == "SPLIT")
    split["children"][1] = split["children"][0]

    def replay(candidate_nodes):
        return leaf.replay(values["source"]["spec"], values["radius"], values["cells"],
                           values["matrix"], values["cap"], values["reference"],
                           values["data"], candidate_nodes, arcs)

    reject("new-closed-split-lost-half", lambda: replay(bad))
    reject("hidden-unreachable-OPEN", lambda: replay(nodes + [{"kind": "OPEN"}]))
    bad = deepcopy(nodes)
    force = next(node for i, node in enumerate(bad)
                 if node["kind"] == "SHARP_FORCE"
                 and (i >= len(values["source"]["nodes"])
                      or values["source"]["nodes"][i]["kind"] == "OPEN"))
    force["cert"]["q"] = 0
    reject("new-force-invalid-denominator", lambda: replay(bad))
    bad_proposal = deepcopy(proposal)
    bad_proposal["radius_scope"] = "at-most-U"
    reject("conditional-tree-promoted-to-U",
           lambda: continuation.proposal_gate(values["source"], paths[0], bad_proposal))
    tiny = [tuple(map(F, row)) for row in values["cap"]["known_candidate_tiny_angle_cells"]]
    retained = any(row["kind"] in ("LOCAL", "SHARP_LOCAL") and all(
        F(lo) <= a <= b <= F(hi) for lo, hi, (a, b) in zip(
            row.get("sharp_lower", row["lower"]), row.get("sharp_upper", row["upper"]), tiny))
        for row in ledger)
    if (not retained
            or F(result["leaf_specific_pinning_maximum_center_error_upper"]) >= F(7, 800000)):
        raise ValueError("continued tree lost the exact root or unchanged local allowance")
    certificate = {
        "schema": "N26-current-candidate-continued-closed-angular-tree-v1",
        "radius_scope": "same-root-Rstar", "spec": values["source"]["spec"],
        "source_acceptance_sha256": manifest["source_acceptance_sha256"], "nodes": nodes}
    for name, value in (("CERTIFICATE.json", certificate), ("PENDING-ANGLES.json", pending),
                        ("LOWER-LEDGER.json", ledger)):
        publish_or_match(folder / name, value)
    old_counts = values["accepted"]["counts"]
    report = {
        "schema": "N26-accepted-current-candidate-angle-continuation-v1",
        "verified": True, **result, "radius_scope": "same-root-Rstar",
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "source_nodes": len(values["source"]["nodes"]),
        "source_OPEN_boxes": len(values["pending"]),
        "prior_all_proved_nodes_and_closed_splits_preserved": True,
        "known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf": retained,
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "new_strict_force_leaves": sum(result["counts"][kind] - old_counts[kind]
                                       for kind in ("FORCE", "SHARP_FORCE", "SHARP_CORRELATED_FORCE")),
        "new_paid_hull_local_leaves": result["counts"][leaf.HULL_LOCAL] - old_counts[leaf.HULL_LOCAL],
        "new_complete_closed_splits": result["counts"]["SPLIT"] - old_counts["SPLIT"],
        "automatically_paid_sharp_empty_indices": empty,
        "automatically_paid_sharp_local_indices": local,
        "negative_controls_rejected": negatives, "discovery_numbers_not_used_as_proof": True,
        "current_global_combinatorial_frontier_nodes_removed": 0,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "files": {name: leaf.sha(folder / name) for name in [
            "MANIFEST.json", *manifest["copied_files"], "CERTIFICATE.json",
            "PENDING-ANGLES.json", "LOWER-LEDGER.json"]},
        "source_files": inventory, "executed_checker_sha256": leaf.sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["continue_current_candidate_angles.py"]:
        raise ValueError("current continuation ran a different checker")
    for text, digest in inventory.items():
        if leaf.sha(leaf.local_path(text)) != digest:
            raise ValueError("candidate dependency changed during exact replay")
    for name, digest in manifest["copied_files"].items():
        if leaf.sha(folder / name) != digest:
            raise ValueError("sealed candidate input changed during exact replay")
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("files", "source_files")}, indent=2), flush=True)


def build(args):
    if args.output.exists():
        raise FileExistsError(args.output)
    source = args.source.resolve()
    accepted, _ = leaf.bound(source)
    args.output.mkdir(parents=True)
    copies = [(source / name, name) for name in accepted["files"] if name.endswith(".py")]
    copies.extend([
        (source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
        (source / "CERTIFICATE.json", "SOURCE-CERTIFICATE.json"),
        (args.proposal, "PROPOSAL.json"),
        (Path(current.__file__), "n26_current_continued_leaf_source.py"),
        (Path(__file__), "continue_current_candidate_angles.py"),
        (Path(__file__).with_name("n26-current-candidate-continuation-proof.md"), "PROOF.md")])
    for original, name in copies:
        (args.output / name).write_bytes(original.read_bytes())
    manifest = {
        "schema": "N26-current-candidate-continuation-bindings-v1",
        "source_acceptance_sha256": leaf.sha(source / "VERIFIED.json"),
        "sources": {key: linux(getattr(args, key.replace("-", "_")).resolve()) for key in INPUTS},
        "copied_files": {name: leaf.sha(args.output / name) for _, name in copies}}
    (args.output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    subprocess.run([sys.executable, str(args.output / "continue_current_candidate_angles.py"),
                    "--input", str(args.output), "--report", str(args.output / "VERIFIED.json")], check=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path)
    parser.add_argument("--report", type=Path)
    for key in (*INPUTS, "proposal", "output"):
        parser.add_argument("--" + key, type=Path)
    args = parser.parse_args()
    if args.input and args.report:
        verify(args.input.resolve(), args.report.resolve())
    elif all(getattr(args, key.replace("-", "_")) for key in (*INPUTS, "proposal", "output")):
        build(args)
    else:
        parser.error("provide --input/--report or all continuation build inputs")


if __name__ == "__main__":
    main()
