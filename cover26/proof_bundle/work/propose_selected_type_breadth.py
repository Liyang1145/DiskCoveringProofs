"""Unaccepted fair breadth-first refinements of every retained competitor box."""

import argparse
from collections import deque
from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import load_trig
from n26_sharp_radius_constraints import constraint_matrix, cap_gate, tighten
from n26_sharp_type_tree import replay
from probe_correlated_arc_force import CorrelatedArcSolver
import verify_terminal_catalog as catalog
from verify_selected_type_trees import SCOPE, bound, read


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--caps", type=Path, required=True)
    parser.add_argument("--seed", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--checks-per-type", type=int, default=4000)
    parser.add_argument("--branch-depth", type=int, default=20)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    bound(args.catalog)
    bound(args.caps)
    values = catalog.input_gate(args.catalog)
    table = catalog.reconstruct(args.catalog, *values[1:])
    if table != read(args.catalog / "CATALOG.json"):
        raise ValueError("breadth-first discovery catalogue did not reconstruct")
    seed = read(args.seed)
    if (seed["schema"] != "N26-unaccepted-selected-canonical-type-sharp-trees-v1"
            or seed["catalog_acceptance_sha256"] != catalog.sha(args.catalog / "VERIFIED.json")
            or seed["cap_acceptance_sha256"] != catalog.sha(args.caps / "VERIFIED.json")
            or seed["radius_scope"] != SCOPE):
        raise ValueError("breadth-first seed changed exact type, caps or conditional scope")
    expected = [i for i, group in enumerate(table["groups"])
                if not any(table["rows"][k]["same_canonical_type_as_known_candidate"] for k in group["member_indices"])]
    if [row["group_index"] for row in seed["proposals"]] != expected:
        raise ValueError("breadth-first seed skipped or duplicated a competitor")
    cap, arcs = read(args.caps / "CERTIFICATE.json"), load_trig(args.caps)[0]
    radius = F(cap["radius_upper"])
    caps, _ = cap_gate(radius, cap, arcs)
    proposals = []
    for previous in seed["proposals"]:
        group_index = previous["group_index"]
        group = table["groups"][group_index]
        spec = {"N": 26, "B": group["B"], "next": 26, "faces": group["canonical_faces"]}
        if previous["spec"] != spec:
            raise ValueError("breadth-first seed graph changed")
        matrix, derivation = constraint_matrix(spec, caps)
        if matrix is None:
            if not previous.get("sharp_domain_empty"):
                raise ValueError("breadth-first seed disagrees on a necessarily empty root")
            proposals.append(previous)
            continue
        nodes = previous["nodes"]
        result, pending, _ = replay(spec, matrix, radius, nodes, arcs)
        if not pending:
            proposals.append(previous)
            continue
        queue = deque((row["index"], list(map(F, row["lower"])), list(map(F, row["upper"])), 0)
                      for row in pending)
        solver, checks = CorrelatedArcSolver(spec), 0
        while queue and checks < args.checks_per_type:
            index, lower, upper, depth = queue.popleft()
            if depth > args.branch_depth:
                continue
            checks += 1
            box = tighten(matrix, lower, upper)
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
                    queue.extend(((children[0], list(lower), left_upper, depth + 1),
                                  (children[1], right_lower, list(upper), depth + 1)))
            if checks % 250 == 0:
                print(json.dumps({"group_index": group_index, "breadth_checks": checks,
                                  "queued_closed_boxes_retained": len(queue), "verified": False}), flush=True)
        result, pending, _ = replay(spec, matrix, radius, nodes, arcs)
        proposals.append({"group_index": group_index, "spec": spec, "nodes": nodes, "checks": checks,
                          "replayed_discovery_counts": result, "pending": pending,
                          "independent_publication_and_source_type_acceptance_pending": True})
        print(json.dumps({"group_index": group_index, "verified": False, **result}), flush=True)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-selected-canonical-type-sharp-trees-v1", "verified": False,
        "catalog_acceptance_sha256": catalog.sha(args.catalog / "VERIFIED.json"),
        "cap_acceptance_sha256": catalog.sha(args.caps / "VERIFIED.json"),
        "radius_scope": SCOPE, "proposals": proposals, "all_unresolved_type_boxes_retained": True,
        "discovery_strategy": "fair-breadth-first-all-retained-closed-boxes",
        "seed_sha256": catalog.sha(args.seed),
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
