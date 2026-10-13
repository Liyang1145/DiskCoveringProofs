"""Unaccepted joint-angle diagnostics and alternative whole-box force proposals."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

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
    parser.add_argument("--per-type", type=int, default=3)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    bound(args.catalog)
    bound(args.caps)
    values = catalog.input_gate(args.catalog)
    table = catalog.reconstruct(args.catalog, *values[1:])
    seed, cap, arcs = read(args.seed), read(args.caps / "CERTIFICATE.json"), load_trig(args.caps)[0]
    if (seed["catalog_acceptance_sha256"] != catalog.sha(args.catalog / "VERIFIED.json")
            or seed["cap_acceptance_sha256"] != catalog.sha(args.caps / "VERIFIED.json")
            or seed["radius_scope"] != SCOPE):
        raise ValueError("joint pending diagnostics changed exact sources")
    radius = F(cap["radius_upper"])
    caps, _ = cap_gate(radius, cap, arcs)
    results = []
    for proposed in seed["proposals"]:
        group = table["groups"][proposed["group_index"]]
        spec = {"N": 26, "B": group["B"], "next": 26, "faces": group["canonical_faces"]}
        if spec != proposed["spec"]:
            raise ValueError("joint pending diagnostics changed a canonical type")
        matrix = constraint_matrix(spec, caps)[0]
        if matrix is None:
            continue
        _, pending, _ = replay(spec, matrix, radius, proposed["nodes"], arcs)
        if not pending:
            continue
        pending.sort(key=lambda row: max(F(b) - F(a) for a, b in zip(row["lower"], row["upper"])))
        indices = sorted({round(i * (len(pending) - 1) / max(args.per_type - 1, 1))
                          for i in range(min(args.per_type, len(pending)))})
        solver = JointAngleSolver(spec)
        for i in indices:
            row = pending[i]
            value = solver.solve_joint(list(map(F, row["lower"])), list(map(F, row["upper"])), matrix, radius)
            results.append({"group_index": proposed["group_index"], "index": row["index"],
                            "lower": row["lower"], "upper": row["upper"], **value})
            print(json.dumps({"group_index": proposed["group_index"], "index": row["index"],
                              **{key: value[key] for key in ("floating_success", "floating_joint_radius",
                                 "floating_constraint_minimum", "proposed_paid_radius_conditional_force")}}), flush=True)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-selected-pending-joint-angle-diagnostics-v1",
        "verified": False, "radius_scope": SCOPE, "radius_upper": str(radius),
        "seed_sha256": catalog.sha(args.seed),
        "catalog_acceptance_sha256": catalog.sha(args.catalog / "VERIFIED.json"),
        "cap_acceptance_sha256": catalog.sha(args.caps / "VERIFIED.json"),
        "results": results, "numerical_radii_are_not_global_lower_bounds": True,
        "all_continuous_cover_or_whole_box_acceptance_obligations_still_required": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
