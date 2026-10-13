"""Scan retained sharp OPEN boxes; no floating result is accepted as proof."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import angular_domain, tighten
from n26_sharp_radius_constraints import tighten as sharp_tighten
from probe_correlated_arc_force import CorrelatedArcSolver
import verify_correlated_candidate_angles as checker


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "historical", "pinning-basis", "stress", "local", "transport",
                 "pinning", "caps", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--checks", type=int, default=10000)
    parser.add_argument("--branch-depth", type=int, default=0)
    parser.add_argument("--seed", type=Path)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    source, report, radius, cells, matrix, cap, pending, inputs = checker.source_gate(
        args.source, args.historical, args.pinning_basis, args.stress, args.local,
        args.transport, args.pinning, args.caps)
    solver = CorrelatedArcSolver(source["spec"])
    nodes, diagnostics = deepcopy(source["nodes"]), []
    if args.seed:
        seed = json.loads(args.seed.read_text())
        if (seed["source_acceptance_sha256"] != checker.sha(args.source / "VERIFIED.json")
                or seed["source_certificate_sha256"] != checker.sha(args.source / "CERTIFICATE.json")):
            raise ValueError("correlated discovery seed has a different accepted source")
        nodes = deepcopy(seed["nodes"])
        checker.lineage_gate(source["nodes"], nodes)
        _, pending, _ = checker.replay(source["spec"], radius, cells, matrix, nodes, solver.arcs)
    stack = [(row["index"], list(map(F, row["lower"])),
              list(map(F, row["upper"])), 0) for row in pending]
    stack.sort(key=lambda row: sum(float(b - a)**2 for a, b in zip(row[1], row[2])))
    old_matrix = angular_domain(source["spec"])
    number = 0
    while stack and number < args.checks:
        index, lower, upper, depth = stack.pop()
        if depth > args.branch_depth:
            continue
        box = tighten(old_matrix, lower, upper)
        number += 1
        if box is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lower, upper = box
        sharp_box = sharp_tighten(matrix, lower, upper)
        if sharp_box is None:
            nodes[index] = {"kind": "SHARP_EMPTY"}
            continue
        lo, hi = sharp_box
        if all(a <= x <= y <= b for x, y, (a, b) in zip(lo, hi, cells)):
            nodes[index] = {"kind": "SHARP_LOCAL"}
            continue
        node, status = solver.solve_correlated(lo, hi, matrix, radius)
        if node is not None:
            nodes[index] = node
        elif depth < args.branch_depth:
            influence = status["anchor_force_norm_proposal"]
            axis = max(range(source["spec"]["B"] - 1),
                       key=lambda i: float(hi[i] - lo[i]) * (influence[i] + 1e-12))
            middle = (lo[axis] + hi[axis]) / 2
            if lower[axis] < middle < upper[axis]:
                children = [len(nodes), len(nodes) + 1]
                nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
                nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(middle), "children": children}
                left_upper, right_lower = list(upper), list(lower)
                left_upper[axis], right_lower[axis] = middle, middle
                stack.extend(((children[0], list(lower), left_upper, depth + 1),
                              (children[1], right_lower, list(upper), depth + 1)))
        diagnostics.append({"index": index, "paid": node is not None, **status})
        if number % 10 == 0:
            print(json.dumps({"unaccepted_boxes_probed": number,
                              "new_direct": sum(node["kind"] == "SHARP_FORCE" for node in nodes)
                                            - report["counts"]["SHARP_FORCE"],
                              "new_correlated": sum(node["kind"] == checker.CORRELATED for node in nodes)}), flush=True)
    checker.lineage_gate(source["nodes"], nodes)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-correlated-candidate-angle-continuation-v1",
        "verified": False, "spec": source["spec"], "radius_scope": "same-root-Rstar",
        "source_acceptance_sha256": checker.sha(args.source / "VERIFIED.json"),
        "source_certificate_sha256": checker.sha(args.source / "CERTIFICATE.json"),
        "nodes": nodes, "discovery_checks": number, "diagnostics": diagnostics,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "proposed_counts": {
        kind: sum(node["kind"] == kind for node in nodes) for kind in checker.KINDS}}), flush=True)


if __name__ == "__main__":
    main()
