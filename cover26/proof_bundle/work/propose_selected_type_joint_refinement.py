"""Unaccepted stationary-angle force refinements; preserve every old split."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import n26_correlated_arc_force as exact_force
from n26_force import load_trig
from n26_sharp_radius_constraints import cap_gate, constraint_matrix
from n26_sharp_type_tree import replay
from probe_free_angle_candidate_rods import JointAngleSolver
from verify_selected_type_trees import SCOPE, bound, read
import verify_terminal_catalog as catalog


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--caps", type=Path, required=True)
    parser.add_argument("--seed", type=Path, required=True)
    parser.add_argument("--cache", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--diagnostics", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists() or args.diagnostics.exists():
        raise FileExistsError("fresh joint-refinement output paths required")
    bound(args.catalog)
    bound(args.caps)
    values = catalog.input_gate(args.catalog)
    table = catalog.reconstruct(args.catalog, *values[1:])
    seed, cap, arcs = read(args.seed), read(args.caps / "CERTIFICATE.json"), load_trig(args.caps)[0]
    source_hashes = {"catalog_acceptance_sha256": catalog.sha(args.catalog / "VERIFIED.json"),
                     "cap_acceptance_sha256": catalog.sha(args.caps / "VERIFIED.json")}
    if (seed["radius_scope"] != SCOPE or any(seed[key] != digest for key, digest in source_hashes.items())):
        raise ValueError("joint refinement changed accepted canonical source or root caps")
    expected = [i for i, group in enumerate(table["groups"])
                if not any(table["rows"][j]["same_canonical_type_as_known_candidate"] for j in group["member_indices"])]
    if [row["group_index"] for row in seed["proposals"]] != expected:
        raise ValueError("joint refinement seed skipped or duplicated a competitor")
    radius = F(cap["radius_upper"])
    caps, _ = cap_gate(radius, cap, arcs)
    cache = {}
    if args.cache:
        cached = read(args.cache)
        if (cached["seed_sha256"] != catalog.sha(args.seed) or cached["radius_scope"] != SCOPE
                or any(cached[key] != digest for key, digest in source_hashes.items())):
            raise ValueError("joint-refinement cache belongs to a different exact domain")
        cache = {(row["group_index"], row["index"]): row for row in cached["results"]}
    proposals, diagnostics, newly_paid = [], [], 0
    for previous in seed["proposals"]:
        group_index, spec = previous["group_index"], previous["spec"]
        group = table["groups"][group_index]
        if spec != {"N": 26, "B": group["B"], "next": 26, "faces": group["canonical_faces"]}:
            raise ValueError("joint refinement changed a complete canonical complex")
        matrix = constraint_matrix(spec, caps)[0]
        if matrix is None:
            if not previous.get("sharp_domain_empty"):
                raise ValueError("joint refinement changed necessary root emptiness")
            proposals.append(previous)
            continue
        nodes = previous["nodes"]
        _, pending, _ = replay(spec, matrix, radius, nodes, arcs)
        if not pending:
            proposals.append(previous)
            continue
        solver, paid = JointAngleSolver(spec), 0
        for number, row in enumerate(pending):
            cached = cache.get((group_index, row["index"]))
            if cached is not None:
                if cached["lower"] != row["lower"] or cached["upper"] != row["upper"]:
                    raise ValueError("cached joint force belongs to a different closed box")
                value = {key: val for key, val in cached.items() if key not in ("group_index", "index", "lower", "upper")}
            else:
                value = solver.solve_joint(list(map(F, row["lower"])), list(map(F, row["upper"])), matrix, radius)
            cert = value.get("force_certificate_proposal")
            accepted_proposal = False
            if cert is not None:
                check = exact_force.force_check(spec, row["lower"], row["upper"], matrix, cert, arcs)
                if F(check["required_radius_lower"]) > radius:
                    if nodes[row["index"]] != {"kind": "OPEN"}:
                        raise ValueError("joint refinement would overwrite an already paid node")
                    nodes[row["index"]] = {"kind": "CORRELATED_FORCE", "cert": cert}
                    paid += 1
                    newly_paid += 1
                    accepted_proposal = True
            diagnostics.append({"group_index": group_index, "index": row["index"],
                                "lower": row["lower"], "upper": row["upper"], **value,
                                "whole_box_force_exactly_rechecked_for_discovery": accepted_proposal})
            print(json.dumps({"group_index": group_index, "OPEN_box_checks": number + 1,
                              "old_OPEN_boxes": len(pending), "new_exact_force_proposals": paid,
                              "floating_joint_radius": value["floating_joint_radius"],
                              "whole_box_exact_force_proposed": accepted_proposal,
                              "verified": False}), flush=True)
        result, remaining, _ = replay(spec, matrix, radius, nodes, arcs)
        proposals.append({"group_index": group_index, "spec": spec, "nodes": nodes,
                          "replayed_discovery_counts": result, "pending": remaining,
                          "new_joint_stationary_force_proposals": paid,
                          "independent_publication_and_source_type_acceptance_pending": True})
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-selected-canonical-type-sharp-trees-v1", "verified": False,
        **source_hashes, "radius_scope": SCOPE, "proposals": proposals,
        "all_unresolved_type_boxes_retained": True,
        "discovery_strategy": "joint-angle-stationary-integer-flow-all-old-OPEN-no-new-splits",
        "seed_sha256": catalog.sha(args.seed), "new_exact_whole_box_force_proposals": newly_paid,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")
    args.diagnostics.write_text(json.dumps({
        "schema": "N26-unaccepted-selected-pending-joint-angle-diagnostics-v1", "verified": False,
        **source_hashes, "radius_scope": SCOPE, "radius_upper": str(radius),
        "seed_sha256": catalog.sha(args.seed), "results": diagnostics,
        "numerical_radii_are_not_global_lower_bounds": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
