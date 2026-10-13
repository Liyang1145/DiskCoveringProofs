"""Unaccepted midpoint/joint refinement with exact inherited-child split scores."""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_correlated_arc_force as force
from n26_force import load_trig
from n26_sharp_radius_constraints import cap_gate, constraint_matrix, tighten
from n26_sharp_type_tree import replay
from probe_correlated_arc_force import CorrelatedArcSolver
from probe_retained_joint_force import RetainingJointSolver, inherited_split
from verify_selected_type_trees import SCOPE, bound, coverage_gate, read
import verify_terminal_catalog as catalog


def main():
    parser = argparse.ArgumentParser()
    for key in ("catalog", "caps", "seed", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--checks-per-type", type=int, default=80)
    parser.add_argument("--branch-depth", type=int, default=10)
    parser.add_argument("--only-groups", type=int, nargs="+")
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    bound(args.catalog)
    bound(args.caps)
    cv = catalog.input_gate(args.catalog)
    table = catalog.reconstruct(args.catalog, *cv[1:])
    seed, cap = read(args.seed), read(args.caps / "CERTIFICATE.json")
    if (seed["radius_scope"] != SCOPE
            or seed["catalog_acceptance_sha256"] != catalog.sha(args.catalog / "VERIFIED.json")
            or seed["cap_acceptance_sha256"] != catalog.sha(args.caps / "VERIFIED.json")):
        raise ValueError("hybrid seed changed full catalogue, radius caps or scope")
    coverage_gate(seed["proposals"], table)
    radius, arcs = F(cap["radius_upper"]), load_trig(args.caps)[0]
    caps, _ = cap_gate(radius, cap, arcs)
    proposals, diagnostics = [], []
    for previous in seed["proposals"]:
        index, spec = previous["group_index"], previous["spec"]
        if previous.get("sharp_domain_empty") or (args.only_groups and index not in args.only_groups):
            proposals.append(previous)
            continue
        matrix = constraint_matrix(spec, caps)[0]
        if matrix is None:
            raise ValueError("hybrid seed omitted sharp root emptiness")
        nodes = deepcopy(previous["nodes"])
        _, pending, _ = replay(spec, matrix, radius, nodes, arcs)
        if not pending:
            proposals.append(previous)
            continue
        queue = deque((row["index"], list(map(F, row["lower"])), list(map(F, row["upper"])), 0)
                      for row in pending)
        midpoint, joint, checks = CorrelatedArcSolver(spec), RetainingJointSolver(spec), 0
        while queue and checks < args.checks_per_type:
            node_index, lower, upper, depth = queue.popleft()
            if depth > args.branch_depth:
                continue
            checks += 1
            box = tighten(matrix, lower, upper)
            if box is None:
                nodes[node_index] = {"kind": "EMPTY"}
                continue
            lower, upper = box
            paid, status = midpoint.solve_correlated(lower, upper, matrix, radius)
            stationary = None
            candidates = []
            if paid is None:
                stationary = joint.solve_retained(lower, upper, matrix, radius)
                cert = stationary["stationary_flow_candidate_retained_even_if_unpaid"]
                if cert is not None:
                    candidates.append(cert)
                    strict = force.force_check(spec, lower, upper, matrix, cert, arcs)
                    if F(strict["required_radius_lower"]) > radius:
                        paid = {"kind": "SHARP_CORRELATED_FORCE", "cert": cert}
            if paid is not None:
                kind = "DIRECT_FORCE" if paid["kind"] == "SHARP_FORCE" else "CORRELATED_FORCE"
                nodes[node_index] = {"kind": kind, "cert": paid["cert"]}
                diagnostics.append({"group_index": index, "index": node_index, "whole_box_paid": True})
                continue
            base = getattr(midpoint, "last_direct_candidate", None)
            if base is not None:
                try:
                    cert, _ = midpoint.difference_dual(lower, upper, matrix, base)
                except ValueError:
                    cert = None
                if cert is not None:
                    candidates.append(cert)
            if depth >= args.branch_depth:
                continue
            trials = [(trial, cert) for cert in candidates for trial in inherited_split(
                spec, matrix, lower, upper, cert, radius, arcs)]
            if trials:
                trial, inherited = max(trials, key=lambda item: (
                    item[0]["paid_children"], F(item[0]["worst_nonempty_child_lower"])
                    if item[0]["worst_nonempty_child_lower"] is not None else F(10)))
                axis, middle = trial["axis"], F(trial["mid"])
            else:
                axis = max(range(len(lower)), key=lambda k: upper[k] - lower[k])
                middle, trial, inherited = (lower[axis] + upper[axis]) / 2, None, None
            if not lower[axis] < middle < upper[axis]:
                continue
            children = [len(nodes), len(nodes) + 1]
            nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
            nodes[node_index] = {"kind": "SPLIT", "axis": axis, "mid": str(middle), "children": children}
            lu, rl = list(upper), list(lower)
            lu[axis], rl[axis] = middle, middle
            for child, lo, hi in ((children[0], list(lower), lu), (children[1], rl, list(upper))):
                child_box = tighten(matrix, lo, hi)
                if child_box is None:
                    nodes[child] = {"kind": "EMPTY"}
                    continue
                lo, hi = child_box
                if inherited is not None:
                    check = force.force_check(spec, lo, hi, matrix, inherited, arcs)
                    if F(check["required_radius_lower"]) > radius:
                        nodes[child] = {"kind": "CORRELATED_FORCE", "cert": inherited}
                        continue
                queue.append((child, lo, hi, depth + 1))
            diagnostics.append({"group_index": index, "index": node_index, "whole_box_paid": False,
                                "chosen_exact_inherited_child_trial": trial})
        for node_index, old in enumerate(previous["nodes"]):
            if old["kind"] != "OPEN" and nodes[node_index] != old:
                raise ValueError("hybrid discovery changed a previous paid node or split")
        result, pending, _ = replay(spec, matrix, radius, nodes, arcs)
        proposals.append({"group_index": index, "spec": spec, "nodes": nodes,
                          "replayed_discovery_counts": result, "pending": pending,
                          "checks": checks, "independent_acceptance_pending": True})
        print(json.dumps({"verified": False, "group_index": index,
                          "hybrid_checks": checks, "nodes": len(nodes),
                          "OPEN": len(pending), "proposed_type_excluded": not pending}), flush=True)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-selected-canonical-type-sharp-trees-v1",
        "verified": False, "radius_scope": SCOPE,
        "catalog_acceptance_sha256": seed["catalog_acceptance_sha256"],
        "cap_acceptance_sha256": seed["cap_acceptance_sha256"],
        "seed_sha256": catalog.sha(args.seed), "proposals": proposals,
        "diagnostics": diagnostics, "all_unresolved_type_boxes_retained": True,
        "strategy": "midpoint-and-retained-joint-flow-exact-worst-child-split-score",
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
