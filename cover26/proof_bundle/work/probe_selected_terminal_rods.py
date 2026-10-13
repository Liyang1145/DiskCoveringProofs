"""Unaccepted numerical searches on independently accepted selected canonical types."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from n26_sharp_radius_constraints import SCALE, constraint_matrix, cap_gate
from n26_force import load_trig
from probe_free_angle_candidate_rods import JointAngleSolver
import verify_terminal_catalog as catalog


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--caps", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted = json.loads((args.catalog / "VERIFIED.json").read_text())
    for name, digest in accepted["files"].items():
        if catalog.sha(args.catalog / name) != digest:
            raise ValueError("selected terminal catalogue bytes changed")
    if not accepted["verified"] or accepted["full_catalog_complete"]:
        raise ValueError("selected terminal discovery scope changed")
    manifest, stage, stage_report, frontier, trace, candidate, runs = catalog.input_gate(args.catalog)
    table = catalog.reconstruct(args.catalog, stage, stage_report, frontier, trace, candidate, runs)
    if table != json.loads((args.catalog / "CATALOG.json").read_text()):
        raise ValueError("selected terminal data did not independently replay")
    cap_report = json.loads((args.caps / "VERIFIED.json").read_text())
    for name, digest in cap_report["files"].items():
        if catalog.sha(args.caps / name) != digest:
            raise ValueError("terminal discovery cap dependency changed")
    cap = json.loads((args.caps / "CERTIFICATE.json").read_text())
    radius = F(cap["radius_upper"])
    caps, margins = cap_gate(radius, cap, load_trig(args.caps)[0])
    results = []
    for index, group in enumerate(table["groups"]):
        spec = {"N": 26, "B": group["B"], "next": 26, "faces": group["canonical_faces"]}
        matrix, derivation = constraint_matrix(spec, caps)
        if matrix is None:
            results.append({"group_index": index, "sharp_domain_infeasible_proposal": True,
                            "derivation": derivation})
            continue
        lower = [F(-matrix[i][0], SCALE) for i in range(1, spec["B"])]
        upper = [F(matrix[0][i], SCALE) for i in range(1, spec["B"])]
        result = JointAngleSolver(spec).solve_joint(lower, upper, matrix, radius, maxiter=280)
        results.append({"group_index": index, "member_indices": group["member_indices"],
                        "spec": spec, **result})
        print(json.dumps({"group_index": index, "member_paths": len(group["member_indices"]),
                          "floating_radius": result["floating_joint_radius"],
                          "floating_constraint_minimum": result["floating_constraint_minimum"],
                          "possible_improvement": result["potential_improvement_requires_independent_continuous_cover_certificate"],
                          "force_leaf_proposed": result["proposed_paid_radius_conditional_force"]}), flush=True)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-selected-terminal-free-rod-search-v1", "verified": False,
        "catalog_acceptance_sha256": catalog.sha(args.catalog / "VERIFIED.json"),
        "caps_acceptance_sha256": catalog.sha(args.caps / "VERIFIED.json"),
        "radius_scope": "same-root-Rstar", "results": results,
        "all_floating_realizations_require_independent_continuous_cover_certification": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
