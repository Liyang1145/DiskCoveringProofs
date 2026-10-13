"""Untrusted retained stationary flows and exact inherited-child diagnostics."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_correlated_arc_force as force
from n26_sharp_radius_constraints import tighten
from probe_free_angle_candidate_rods import JointAngleSolver
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import sha


class RetainingJointSolver(JointAngleSolver):
    def difference_dual(self, lower, upper, matrix, base):
        certificate, diagnostic = super().difference_dual(lower, upper, matrix, base)
        self.stationary_certificate = deepcopy(certificate)
        self.stationary_base = deepcopy(base)
        return certificate, diagnostic

    def solve_retained(self, lower, upper, matrix, radius):
        self.stationary_certificate = None
        self.stationary_base = None
        record = self.solve_joint(lower, upper, matrix, radius)
        record["stationary_flow_candidate_retained_even_if_unpaid"] = self.stationary_certificate
        return record


def inherited_split(spec, matrix, lower, upper, certificate, radius, arcs, axes=5):
    """Compare strict whole-child payments; numerical objectives never pay."""
    lower, upper = list(map(F, lower)), list(map(F, upper))
    choices = sorted(range(len(lower)), key=lambda i: upper[i] - lower[i], reverse=True)[:axes]
    trials = []
    for axis in choices:
        middle = (lower[axis] + upper[axis]) / 2
        if not lower[axis] < middle < upper[axis]:
            continue
        lu, rl = list(upper), list(lower)
        lu[axis], rl[axis] = middle, middle
        children = []
        for lo, hi in ((lower, lu), (rl, upper)):
            box = tighten(matrix, lo, hi)
            if box is None:
                children.append({"kind": "EMPTY"})
                continue
            lo, hi = box
            result = force.force_check(spec, lo, hi, matrix, certificate, arcs)
            lb = F(result["required_radius_lower"])
            children.append({"kind": "CORRELATED_FORCE" if lb > radius else "OPEN",
                             "lower": list(map(str, lo)), "upper": list(map(str, hi)),
                             "required_radius_lower": str(lb), "strict_margin": str(lb - radius)})
        finite = [F(row["required_radius_lower"]) for row in children if row["kind"] != "EMPTY"]
        trials.append({"axis": axis, "mid": str(middle), "children": children,
                       "paid_children": sum(row["kind"] != "OPEN" for row in children),
                       "worst_nonempty_child_lower": str(min(finite)) if finite else None})
    trials.sort(key=lambda row: (row["paid_children"], F(row["worst_nonempty_child_lower"])
                                if row["worst_nonempty_child_lower"] is not None else F(10)), reverse=True)
    return trials


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--pool", type=Path, required=True)
    parser.add_argument("--pool-replay", type=Path, required=True)
    parser.add_argument("--per-type", type=int, default=2)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = bound(args.pool)
    if read(args.pool_replay) != accepted:
        raise ValueError("retained-flow discovery requires an actual matching proof-pool replay")
    radius = F(accepted["radius_upper"])
    domains = {row["group_index"]: row["matrix"] for row in read(args.pool / "DOMAINS.json")}
    pending = read(args.pool / "PENDING-TYPES.json")
    records = []
    for group in pending:
        boxes = sorted(group["closed_OPEN_boxes"], key=lambda row:
                       sum((F(b) - F(a))**2 for a, b in zip(row["lower"], row["upper"])), reverse=True)
        if not boxes:
            continue
        solver = RetainingJointSolver(group["spec"])
        matrix = domains[group["group_index"]]
        for row in boxes[:args.per_type]:
            record = solver.solve_retained(list(map(F, row["lower"])), list(map(F, row["upper"])), matrix, radius)
            certificate = record["stationary_flow_candidate_retained_even_if_unpaid"]
            trials = inherited_split(group["spec"], matrix, row["lower"], row["upper"],
                                     certificate, radius, solver.arcs) if certificate else []
            records.append({"group_index": group["group_index"], "index": row["index"],
                            "lower": row["lower"], "upper": row["upper"],
                            **record, "inherited_stationary_flow_closed_child_trials": trials})
            print(json.dumps({"verified": False, "group_index": group["group_index"], "index": row["index"],
                              "whole_box_paid": record["proposed_paid_radius_conditional_force"],
                              "best_inherited_split_paid_children": trials[0]["paid_children"] if trials else None,
                              "best_inherited_split_axis": trials[0]["axis"] if trials else None}), flush=True)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-retained-joint-force-split-diagnostics-v1",
        "verified": False, "radius_scope": accepted["radius_scope"],
        "pool_acceptance_sha256": sha(args.pool / "VERIFIED.json"),
        "actual_pool_replay_matched": True, "results": records,
        "numerical_objectives_are_not_lower_bounds": True,
        "new_closed_split_tree_and_independent_acceptance_still_required": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
