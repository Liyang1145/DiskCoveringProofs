"""Unaccepted retained stationary flows on current broad candidate OPEN boxes."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import load_trig
from n26_sharp_radius_constraints import cap_gate, constraint_matrix
import n26_correlated_arc_force as force
from probe_retained_joint_force import RetainingJointSolver, inherited_split
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import sha


def main():
    parser = argparse.ArgumentParser()
    for key in ("source", "overlay", "caps", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--limit", type=int, default=12)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    source, _ = bound(args.source)
    overlay, _ = bound(args.overlay)
    bound(args.caps)
    if (overlay["source_acceptance_sha256"] != sha(args.source / "VERIFIED.json")
            or overlay["radius_scope"] != "same-root-Rstar"
            or not overlay["all_unpaid_source_OPEN_boxes_retained_unchanged"]):
        raise ValueError("retained candidate discovery changed current source or paid overlay")
    spec = read(args.source / "CERTIFICATE.json")["spec"]
    cap = read(args.caps / "CERTIFICATE.json")
    radius, arcs = F(cap["radius_upper"]), load_trig(args.caps)[0]
    caps, _ = cap_gate(radius, cap, arcs)
    matrix = constraint_matrix(spec, caps)[0]
    if matrix != read(args.caps / "MATRIX.json") or str(radius) != overlay["radius_upper"]:
        raise ValueError("retained candidate discovery changed graph matrix or same root radius")
    pending = read(args.overlay / "PENDING-ANGLES.json")
    pending.sort(key=lambda row: sum((F(b) - F(a))**2 for a, b in zip(
        row["sharp_lower"], row["sharp_upper"])), reverse=True)
    solver, results = RetainingJointSolver(spec), []
    for row in pending[:args.limit]:
        lo, hi = list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"]))
        value = solver.solve_retained(lo, hi, matrix, radius)
        certificate = value["stationary_flow_candidate_retained_even_if_unpaid"]
        trials = inherited_split(spec, matrix, lo, hi, certificate, radius, arcs) if certificate else []
        margin = F(force.force_check(spec, lo, hi, matrix, certificate, arcs)["required_radius_lower"]) - radius if certificate else None
        results.append({"index": row["index"], "sharp_lower": row["sharp_lower"],
                        "sharp_upper": row["sharp_upper"], **value,
                        "exact_whole_box_force_margin": str(margin) if margin is not None else None,
                        "inherited_closed_child_trials": trials})
        print(json.dumps({"verified": False, "index": row["index"],
                          "numeric_joint_radius_not_a_global_bound": value["floating_joint_radius"],
                          "strict_whole_box_force_proposed": margin is not None and margin > 0,
                          "best_inherited_split_paid_children": trials[0]["paid_children"] if trials else None}), flush=True)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-retained-broad-candidate-force-diagnostics-v1",
        "verified": False, "source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
        "overlay_acceptance_sha256": sha(args.overlay / "VERIFIED.json"),
        "cap_acceptance_sha256": sha(args.caps / "VERIFIED.json"),
        "radius_scope": "same-root-Rstar", "results": results,
        "independent_current_tree_overlay_acceptance_pending": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
