"""Unaccepted closed continuation of all leaf-pinned OPEN source boxes."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import angular_domain, tighten
from n26_sharp_radius_constraints import tighten as sharp_tighten
from probe_correlated_arc_force import CorrelatedArcSolver
import n26_current_leaf_angle_source as current


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--checks", type=int, default=1000)
    parser.add_argument("--branch-depth", type=int, default=60)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    out = Path(__file__).resolve().parent.parent / "outputs"
    values = current.input_gate(
        args.source, out / "n26-correlated-candidate-angles-v1",
        out / "n26-sharp-constraint-candidate-angles-v2", out / "n26-continued-candidate-angles-v1",
        out / "n26-anchor-pinning-v3", out / "n26-positive-stress-v1",
        out / "n26-centered-local-barrier-v2", out / "n26-candidate-transport-control-v1",
        out / "n26-refined-anchor-pinning-v2", out / "n26-sharp-radius-angle-caps-v2")
    source, accepted = values["source"], values["accepted"]
    radius, cells, matrix = values["radius"], values["cells"], values["matrix"]
    nodes, diagnostics = deepcopy(source["nodes"]), []
    tiny = [tuple(map(F, row)) for row in values["cap"]["known_candidate_tiny_angle_cells"]]
    center = [(a + b) / 2 for a, b in tiny]
    stack = [(row["index"], list(map(F, row["lower"])),
              list(map(F, row["upper"])), 0) for row in values["pending"]]
    stack.sort(key=lambda row: sum(float(b - a)**2 for a, b in zip(row[1], row[2])), reverse=True)
    old_matrix, solver = angular_domain(source["spec"]), CorrelatedArcSolver(source["spec"])
    count = 0
    while stack and count < args.checks:
        index, lower, upper, depth = stack.pop()
        if depth > args.branch_depth:
            continue
        count += 1
        original = tighten(old_matrix, lower, upper)
        if original is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lower, upper = original
        sharper = sharp_tighten(matrix, lower, upper)
        if sharper is None:
            nodes[index] = {"kind": "SHARP_EMPTY"}
            continue
        lo, hi = sharper
        if all(a <= x <= y <= b for x, y, (a, b) in zip(lo, hi, cells)):
            nodes[index] = {"kind": "SHARP_LOCAL"}
            continue
        if max(max(abs(a - c), abs(b - c)) for a, b, c in zip(lo, hi, center)) < F(1, 100000):
            pin = deepcopy(values["reference"])
            pin["closed_anchor_angle_cells"] = [[str(min(a, x)), str(max(b, y))]
                                                for a, b, (x, y) in zip(lo, hi, tiny)]
            try:
                current.leaf.refined.derive(*values["data"][:5], pin)
            except ValueError:
                pass
            else:
                nodes[index] = {"kind": current.leaf.HULL_LOCAL}
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
                child_boxes = [(children[0], list(lower), left_upper, depth + 1),
                               (children[1], right_lower, list(upper), depth + 1)]
                child_boxes.sort(key=lambda row: sum(float((a + b) / 2 - c)**2
                                                      for a, b, c in zip(row[1], row[2], center)))
                stack.extend(child_boxes)
        diagnostics.append({"index": index, "paid": node is not None, **status})
        if count % 40 == 0:
            print(json.dumps({"unaccepted_continued_boxes": count, "nodes": len(nodes),
                              "new_force": sum(node["kind"] in ("FORCE", "SHARP_FORCE", "SHARP_CORRELATED_FORCE")
                                               for node in nodes)
                                           - sum(accepted["counts"][kind] for kind in
                                                 ("FORCE", "SHARP_FORCE", "SHARP_CORRELATED_FORCE")),
                              "new_hull_local": sum(node["kind"] == current.leaf.HULL_LOCAL for node in nodes)
                                                - accepted["counts"][current.leaf.HULL_LOCAL]}), flush=True)
    current.leaf.lineage_gate(source["nodes"], nodes)
    proposal = {"schema": "N26-unaccepted-continued-leaf-pinned-angular-tree-v1",
                "verified": False, "radius_scope": "same-root-Rstar", "spec": source["spec"],
                "source_acceptance_sha256": current.leaf.sha(args.source / "VERIFIED.json"),
                "source_certificate_sha256": current.leaf.sha(args.source / "CERTIFICATE.json"),
                "nodes": nodes, "discovery_checks": count, "diagnostics": diagnostics,
                "global_optimality_proved": False}
    args.output.write_text(json.dumps(proposal, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "proposed_counts": {
        kind: sum(node["kind"] == kind for node in nodes) for kind in current.leaf.KINDS}}), flush=True)


if __name__ == "__main__":
    main()
