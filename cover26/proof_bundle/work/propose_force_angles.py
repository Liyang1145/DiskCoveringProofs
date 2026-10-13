"""Untrusted adaptive angular splitting with exact candidate leaf replays."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from n26_force import CAPS, D, angular_domain, rootbox, tighten
from n26_force_angles import verify_angular_tree
from probe_n26_force import Solver


WORK = Path(__file__).resolve().parent


def propose_angular_tree(spec, max_checks=63, progress=False, root_solution=None):
    matrix = angular_domain(spec)
    lower, upper = rootbox(matrix)
    solver = Solver(spec)
    nodes = [{"kind": "OPEN"}]
    stack = [(0, lower, upper)]
    checks = 0
    while stack and checks < max_checks:
        index, lower, upper = stack.pop()
        box = tighten(matrix, lower, upper)
        checks += 1
        if box is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lower, upper = box
        cert, status = (root_solution if index == 0 and root_solution is not None
                        else solver.solve(lower, upper))
        if cert is not None:
            nodes[index] = {"kind": "FORCE", "cert": cert}
        else:
            widths = [float(hi - lo) for lo, hi in zip(lower, upper)]
            norms = status["anchor_norms_proposal"]
            candidates = [i for i, width in enumerate(widths) if width > 0]
            if not candidates:
                stack.append((index, lower, upper))
                break
            axis = max(candidates, key=lambda i: widths[i] * (max(0., 1 - norms[i]) + 1e-12))
            mid = (lower[axis] + upper[axis]) / 2
            children = [len(nodes), len(nodes) + 1]
            nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
            nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(mid), "children": children}
            left_upper, right_lower = list(upper), list(lower)
            left_upper[axis] = mid
            right_lower[axis] = mid
            stack.extend(((children[1], right_lower, list(upper)),
                          (children[0], list(lower), left_upper)))
        if progress and checks % 10 == 0:
            print(json.dumps({"angular_boxes_probed": checks, "pending_boxes": len(stack),
                              "allocated_nodes": len(nodes)}), flush=True)
    closed = not stack and all(node["kind"] != "OPEN" for node in nodes)
    exact = verify_angular_tree(spec, nodes, solver.arcs) if closed else None
    return {"proposed_closed": closed, "checks": checks, "nodes": nodes,
            "exact_candidate_replay": exact, "pending_boxes": len(stack)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=11)
    parser.add_argument("--checks", type=int, default=127)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    diagnostic = json.loads((WORK / "n26-B14-adaptive-area-proposals-v1.json").read_text())
    prefix = tuple(diagnostic["events"][-1]["prefix"][:args.depth])
    reference = OriginReference(26, 14, "dfs", caps=CAPS, scale=D)
    state = reference.resolve(prefix)
    spec = {"N": 26, "B": 14, "next": state.next_vertex, "faces": list(state.faces)}
    result = propose_angular_tree(spec, args.checks, progress=True)
    args.output.write_text(json.dumps({"verified": False, "prefix": list(prefix), "spec": spec,
                                       **result, "global_optimality_proved": False}, separators=(",", ":")) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key != "nodes"}), flush=True)


if __name__ == "__main__":
    main()
