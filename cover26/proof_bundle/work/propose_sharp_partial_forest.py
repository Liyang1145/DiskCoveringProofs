"""Unaccepted root scan and sharp closed trees on actual partial U subtrees."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import load_trig
import n26_sharp_radius_constraints as constraints
import n26_sharp_partial_domains as independent
from n26_sharp_type_tree import replay, rootbox
from probe_correlated_arc_force import CorrelatedArcSolver
from verify_selected_type_trees import SCOPE, bound, read
from verify_terminal_catalog import sha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--caps", type=Path, required=True)
    parser.add_argument("--types", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-force-roots", type=int, default=80)
    parser.add_argument("--checks-per-root", type=int, default=15)
    parser.add_argument("--branch-depth", type=int, default=10)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    stage, _ = bound(args.stage)
    cap_report, _ = bound(args.caps)
    types, _ = bound(args.types)
    frontier, cap = read(args.stage / "FRONTIER.json"), read(args.caps / "CERTIFICATE.json")
    if frontier["families"] != stage["families"] or types["radius_scope"] != SCOPE:
        raise ValueError("partial sharp discovery source changed")
    arcs = load_trig(args.caps)[0]
    radius = F(cap["radius_upper"])
    caps, _ = constraints.cap_gate(radius, cap, arcs)
    if (cap_report["source_stress_acceptance_sha256"] != types["source_acceptance_sha256"]["stress"]
            or types["source_acceptance_sha256"]["caps"] != sha(args.caps / "VERIFIED.json")
            or F(types["radius_upper"]) != radius):
        raise ValueError("partial sharp discovery changed the certified root radius")
    classification = read(args.types / "CLASSIFICATION.json")
    already_paid = {(member["B"], tuple(member["prefix"])) for row in classification
                    if row["radius_at_most_Rstar_type_excluded"] for member in row["members"]}
    candidate = read(args.types / "CATALOG-SOURCE/CANDIDATE-PATH.json")["prefix"]
    roots, active, matrices = [], [], {}
    for index, state in enumerate(frontier["pending_states"]):
        spec = {"N": 26, "B": state["B"], "next": state["next"], "faces": state["faces"]}
        matrix, _ = constraints.constraint_matrix(spec, caps)
        alternative, _ = independent.matrix(spec, caps)
        if matrix != alternative:
            raise ValueError("independent partial sharp matrices disagree")
        key = (state["B"], tuple(state["prefix"]))
        if key in already_paid:
            continue
        if state["B"] == 16 and candidate[:len(state["prefix"])] == state["prefix"]:
            if matrix is None:
                raise ValueError("sharp necessary constraints rejected a known candidate owner")
            continue
        if matrix is None:
            roots.append({"source_index": index, "B": state["B"], "prefix": state["prefix"],
                          "spec": spec, "sharp_domain_empty": True})
        else:
            active.append((index, state))
            matrices[index] = matrix
        if (index + 1) % 400 == 0:
            print(json.dumps({"all_source_sharp_roots_scanned": index + 1,
                              "conditional_necessary_root_empties": len(roots)}), flush=True)
    active.sort(key=lambda pair: (-len(pair[1]["faces"]), -pair[1]["next"],
                                 pair[1]["B"], pair[1]["prefix"]))
    for ordinal, (source_index, state) in enumerate(active[:args.max_force_roots]):
        spec = {"N": 26, "B": state["B"], "next": state["next"], "faces": state["faces"]}
        matrix = matrices[source_index]
        lower, upper = rootbox(matrix)
        nodes, stack, checks = [{"kind": "OPEN"}], [(0, lower, upper, 0)], 0
        solver = CorrelatedArcSolver(spec)
        while stack and checks < args.checks_per_root:
            index, lower, upper, depth = stack.pop()
            if depth > args.branch_depth:
                continue
            checks += 1
            box = constraints.tighten(matrix, lower, upper)
            if box is None:
                nodes[index] = {"kind": "EMPTY"}
                continue
            lower, upper = box
            proposed, status = solver.solve_correlated(lower, upper, matrix, radius)
            if proposed is not None:
                kind = "DIRECT_FORCE" if proposed["kind"] == "SHARP_FORCE" else "CORRELATED_FORCE"
                nodes[index] = {"kind": kind, "cert": proposed["cert"]}
            elif depth < args.branch_depth:
                influence = status["anchor_force_norm_proposal"]
                axis = max(range(spec["B"] - 1),
                           key=lambda k: float(upper[k] - lower[k]) * (influence[k] + 1e-12))
                middle = (lower[axis] + upper[axis]) / 2
                if lower[axis] < middle < upper[axis]:
                    children = [len(nodes), len(nodes) + 1]
                    nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
                    nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(middle), "children": children}
                    left_upper, right_lower = list(upper), list(lower)
                    left_upper[axis], right_lower[axis] = middle, middle
                    stack.extend(((children[0], list(lower), left_upper, depth + 1),
                                  (children[1], right_lower, list(upper), depth + 1)))
        result, pending, _ = replay(spec, matrix, radius, nodes, arcs)
        roots.append({"source_index": source_index, "B": state["B"], "prefix": state["prefix"],
                      "spec": spec, "nodes": nodes, "checks": checks,
                      "discovery_result": result, "pending": pending})
        print(json.dumps({"force_roots_checked": ordinal + 1, "source_index": source_index,
                          "B": state["B"], "partial_faces": len(state["faces"]), **result}), flush=True)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-sharp-partial-subtree-forest-v1", "verified": False,
        "radius_scope": SCOPE, "radius_upper": str(radius),
        "source_stage_acceptance_sha256": sha(args.stage / "VERIFIED.json"),
        "source_cap_acceptance_sha256": sha(args.caps / "VERIFIED.json"),
        "source_type_acceptance_sha256": sha(args.types / "VERIFIED.json"),
        "all_source_necessary_root_domains_independently_scanned": len(frontier["pending_states"]),
        "all_unattempted_subtrees_retained": True,
        "known_candidate_and_already_certified_type_members_not_reprocessed": True,
        "roots": roots, "global_optimality_proved": False},
        separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
