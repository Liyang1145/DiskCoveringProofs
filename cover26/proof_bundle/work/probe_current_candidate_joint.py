"""Unaccepted no-split joint-angle attempts on the newly accepted candidate tree."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import continue_current_candidate_angles as source_checker
import n26_correlated_arc_force as exact_force
from n26_force import load_trig
from probe_free_angle_candidate_rods import JointAngleSolver


leaf = source_checker.leaf


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=24)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--diagnostics", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists() or args.diagnostics.exists():
        raise FileExistsError("fresh candidate joint discovery paths required")
    accepted, inventory = leaf.bound(args.source)
    if (accepted["schema"] != "N26-accepted-current-candidate-angle-continuation-v1"
            or leaf.sha(source_checker.__file__) != accepted["files"]["continue_current_candidate_angles.py"]):
        raise ValueError("candidate joint discovery imported a different accepted source checker")
    manifest, paths, old, source_proposal = source_checker.input_gate(args.source)
    arcs = load_trig(args.source)[0]
    nodes, result, pending, ledger, empty, local = source_checker.continuation.replay_and_close(
        old, source_proposal, arcs)
    source = {
        "schema": "N26-current-candidate-continued-closed-angular-tree-v1",
        "radius_scope": "same-root-Rstar", "spec": old["source"]["spec"],
        "source_acceptance_sha256": manifest["source_acceptance_sha256"], "nodes": nodes}
    if (source != source_checker.read(args.source / "CERTIFICATE.json")
            or pending != source_checker.read(args.source / "PENDING-ANGLES.json")
            or ledger != source_checker.read(args.source / "LOWER-LEDGER.json")
            or any(accepted[key] != value for key, value in result.items())
            or empty != accepted["automatically_paid_sharp_empty_indices"]
            or local != accepted["automatically_paid_sharp_local_indices"]):
        raise ValueError("current accepted candidate extension did not semantically reconstruct")
    pending.sort(key=lambda row: sum((F(b) - F(a))**2 for a, b in zip(
        row["sharp_lower"], row["sharp_upper"])))
    solver = JointAngleSolver(source["spec"])
    proposed_nodes, diagnostics, paid = deepcopy(nodes), [], 0
    for row in pending[:args.limit]:
        lower, upper = row["sharp_lower"], row["sharp_upper"]
        value = solver.solve_joint(list(map(F, lower)), list(map(F, upper)), old["matrix"], old["radius"])
        cert = value.get("force_certificate_proposal")
        margin = None
        if cert is not None:
            check = exact_force.force_check(source["spec"], lower, upper, old["matrix"], cert, arcs)
            margin = F(check["required_radius_lower"]) - old["radius"]
            if margin > 0:
                if proposed_nodes[row["index"]] != {"kind": "OPEN"}:
                    raise ValueError("candidate joint discovery would overwrite a paid node")
                proposed_nodes[row["index"]] = {"kind": "SHARP_CORRELATED_FORCE", "cert": cert}
                paid += 1
        diagnostics.append({"index": row["index"], "sharp_lower": lower, "sharp_upper": upper,
                            **value, "discovery_whole_box_strict_margin": str(margin) if margin is not None else None})
        print(json.dumps({"verified": False, "candidate_joint_boxes_checked": len(diagnostics),
                          "new_whole_box_force_proposals": paid,
                          "floating_joint_radius_not_a_global_lower_bound": value["floating_joint_radius"]}),
              flush=True)
    leaf.lineage_gate(nodes, proposed_nodes)
    proposal = {
        "schema": "N26-unaccepted-current-candidate-leaf-continuation-v1",
        "verified": False, "radius_scope": "same-root-Rstar", "spec": source["spec"],
        "source_acceptance_sha256": leaf.sha(args.source / "VERIFIED.json"),
        "source_certificate_sha256": leaf.sha(args.source / "CERTIFICATE.json"),
        "all_prior_non_OPEN_nodes_and_closed_splits_preserved": True,
        "nodes": proposed_nodes, "discovery_checks": len(diagnostics),
        "new_joint_whole_box_force_proposals": paid, "new_splits": 0,
        "independent_current_source_loader_and_acceptance_still_required": True,
        "global_optimality_proved": False}
    args.output.write_text(json.dumps(proposal, separators=(",", ":")) + "\n", encoding="utf-8")
    args.diagnostics.write_text(json.dumps({
        "schema": "N26-unaccepted-current-candidate-joint-angle-diagnostics-v1",
        "verified": False, "source_acceptance_sha256": proposal["source_acceptance_sha256"],
        "all_numerical_radii_are_not_global_lower_bounds": True,
        "results": diagnostics, "global_optimality_proved": False},
        separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
