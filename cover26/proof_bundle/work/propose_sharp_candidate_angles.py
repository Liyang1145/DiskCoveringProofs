"""Untrusted SLSQP discovery for sharp FORCE/LOCAL/OPEN angle classification."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
from n26_force import tighten, angular_domain
import n26_sharp_candidate_angles as sharp
from probe_direct_arc_force import DirectArcSolver


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--local", type=Path, required=True)
    parser.add_argument("--transport", type=Path, required=True)
    parser.add_argument("--pinning", type=Path, required=True)
    parser.add_argument("--checks", type=int, default=400)
    parser.add_argument("--branch-depth", type=int, default=24)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    spec, radius_upper, cells, sources, _ = sharp.input_gate(
        args.stress, args.local, args.transport, args.pinning)
    matrix = angular_domain(spec)
    nodes, seeded = sharp.seeded_partition(spec, cells)
    stack = [(index, lo, hi, 0) for index, lo, hi in seeded]
    solver = DirectArcSolver(spec)
    checks, diagnostics = 0, []
    while stack and checks < args.checks:
        index, lower, upper, branch_depth = stack.pop()
        if branch_depth >= args.branch_depth:
            continue
        box = tighten(matrix, lower, upper)
        checks += 1
        if box is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lower, upper = box
        cert, status = solver.solve_sharp(lower, upper, radius_upper)
        diagnostics.append({"node_index": index, **status})
        if cert is not None:
            nodes[index] = {"kind": "FORCE", "cert": cert}
        else:
            widths = [float(b - a) for a, b in zip(lower, upper)]
            axis = max(range(15), key=lambda i: widths[i] * (status["anchor_force_norm_proposal"][i] + 1e-12))
            mid = (lower[axis] + upper[axis]) / 2
            if not lower[axis] < mid < upper[axis]:
                stack.append((index, lower, upper, branch_depth))
                break
            children = [len(nodes), len(nodes) + 1]
            nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
            nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(mid), "children": children}
            left_upper, right_lower = list(upper), list(lower)
            left_upper[axis], right_lower[axis] = mid, mid
            branches = [
                (children[1], right_lower, list(upper), branch_depth + 1),
                (children[0], list(lower), left_upper, branch_depth + 1),
            ]
            # Explore the farther half first; every skipped/depth-limited leaf
            # stays OPEN in the complete tree, regardless of this heuristic.
            def distance(row):
                return sum(float((a + b - c - d) / 2)**2
                           for a, b, (c, d) in zip(row[1], row[2], cells))
            stack.extend(sorted(branches, key=distance))
        if checks % 20 == 0:
            print(json.dumps({"candidate_angle_boxes_probed": checks,
                              "pending_boxes": len(stack), "allocated_nodes": len(nodes),
                              "force_leaves": sum(n["kind"] == "FORCE" for n in nodes)}), flush=True)
    result, pending, ledger = sharp.replay(spec, radius_upper, cells, nodes, solver.arcs)
    proposal = {
        "schema": "N26-sharp-candidate-partial-angle-partition-proposal-v1",
        "verified": False, "radius_scope": "same-root-Rstar", "spec": spec,
        "source_acceptance_sha256": sources, "nodes": nodes,
        "discovery_checks": checks, "discovery_branch_depth_limit": args.branch_depth,
        "diagnostics": diagnostics,
        "candidate_transport_global_lower_bound_proved": result["candidate_transport_global_lower_bound_proved"],
        "global_optimality_proved": False,
    }
    args.output.write_text(json.dumps(proposal, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, **result}), flush=True)


if __name__ == "__main__":
    main()
