"""Untrusted continuation from all retained OPEN leaves of the refined tree."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import angular_domain, tighten
from probe_direct_arc_force import DirectArcSolver
import verify_refined_candidate_angles as accepted_checker


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--accepted", type=Path, required=True)
    parser.add_argument("--prior", type=Path, required=True)
    parser.add_argument("--pinning-basis", type=Path, required=True)
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--local", type=Path, required=True)
    parser.add_argument("--transport", type=Path, required=True)
    parser.add_argument("--pinning", type=Path, required=True)
    parser.add_argument("--checks", type=int, default=240)
    parser.add_argument("--branch-depth", type=int, default=18)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = accepted_checker.bound(args.accepted)
    if accepted_checker.sharp.pin.sha(accepted_checker.__file__) != accepted["files"]["verify_refined_candidate_angles.py"]:
        raise ValueError("untrusted continuation loaded a changed accepted tree reconstructor")
    source, source_result, pending, _, _, pin_result, _, _ = accepted_checker.reconstruct(
        args.prior, args.pinning_basis, args.stress, args.local, args.transport, args.pinning)
    if (source != json.loads((args.accepted / "CERTIFICATE.json").read_text())
            or any(accepted[key] != value for key, value in source_result.items())):
        raise ValueError("continuation did not reconstruct the accepted refined angular frontier")
    nodes = deepcopy(source["nodes"])
    spec = source["spec"]
    matrix = angular_domain(spec)
    cells = [tuple(map(F, row)) for row in pin_result["closed_anchor_angle_cells"]]
    center = [(a + b) / 2 for a, b in cells]
    radius_upper = F(json.loads((args.stress / "VERIFIED.json").read_text())["modified_root_check"]["r_strict_interval"][1])
    stack = [(r["index"], list(map(F, r["lower"])), list(map(F, r["upper"])), 0) for r in pending]
    stack.sort(key=lambda r: sum(float(b - a)**2 for a, b in zip(r[1], r[2])), reverse=True)
    solver = DirectArcSolver(spec)
    checks, diagnostics = 0, []
    while stack and checks < args.checks:
        index, lower, upper, depth = stack.pop()
        if depth >= args.branch_depth:
            continue
        box = tighten(matrix, lower, upper)
        checks += 1
        if box is None:
            nodes[index] = {"kind": "EMPTY"}
            continue
        lower, upper = box
        if all(a <= lo <= hi <= b for lo, hi, (a, b) in zip(lower, upper, cells)):
            nodes[index] = {"kind": "LOCAL"}
            continue
        cert, status = solver.solve_sharp(lower, upper, radius_upper)
        diagnostics.append({"node_index": index, **status})
        if cert is not None:
            nodes[index] = {"kind": "FORCE", "cert": cert}
        else:
            widths = [float(b - a) for a, b in zip(lower, upper)]
            axis = max(range(15), key=lambda i: widths[i] * (status["anchor_force_norm_proposal"][i] + 1e-12))
            middle = (lower[axis] + upper[axis]) / 2
            if not lower[axis] < middle < upper[axis]:
                continue
            children = [len(nodes), len(nodes) + 1]
            nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
            nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(middle), "children": children}
            left_upper, right_lower = list(upper), list(lower)
            left_upper[axis], right_lower[axis] = middle, middle
            branches = [
                (children[0], list(lower), left_upper, depth + 1),
                (children[1], right_lower, list(upper), depth + 1),
            ]
            branches.sort(key=lambda r: sum(float((a + b) / 2 - c)**2
                                           for a, b, c in zip(r[1], r[2], center)))
            stack.extend(branches)
        if checks % 20 == 0:
            print(json.dumps({"continued_angle_boxes_probed": checks,
                              "nodes": len(nodes), "allocated_OPEN": sum(n["kind"] == "OPEN" for n in nodes),
                              "FORCE": sum(n["kind"] == "FORCE" for n in nodes),
                              "LOCAL": sum(n["kind"] == "LOCAL" for n in nodes)}), flush=True)
    # This is discovery replay only. Publication requires a separate lineage
    # and standalone exact acceptance of the whole continued tree.
    result, remaining, ledger = accepted_checker.sharp.replay(spec, radius_upper, cells, nodes, solver.arcs)
    proposal = {
        "schema": "N26-untrusted-refined-candidate-angle-continuation-v1",
        "verified": False, "radius_scope": "same-root-Rstar", "spec": spec,
        "refinement_source_acceptance_sha256": accepted_checker.sharp.pin.sha(args.accepted / "VERIFIED.json"),
        "refinement_source_certificate_sha256": accepted_checker.sharp.pin.sha(args.accepted / "CERTIFICATE.json"),
        "refinement_source_original_path": str(args.accepted),
        "source_acceptance_sha256": source["source_acceptance_sha256"],
        "nodes": nodes, "discovery_checks": checks, "branch_depth_limit": args.branch_depth,
        "diagnostics": diagnostics, "candidate_replay_result": result,
        "global_optimality_proved": False,
    }
    args.output.write_text(json.dumps(proposal, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, **result}), flush=True)


if __name__ == "__main__":
    main()
