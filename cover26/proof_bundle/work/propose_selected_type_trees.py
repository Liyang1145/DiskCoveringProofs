"""Unaccepted full-domain attempts for every selected noncandidate canonical type."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import load_trig
from n26_sharp_radius_constraints import constraint_matrix, cap_gate, tighten
from n26_sharp_type_tree import rootbox, replay
from probe_correlated_arc_force import CorrelatedArcSolver
import verify_terminal_catalog as catalog


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--caps", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--checks-per-type", type=int, default=300)
    parser.add_argument("--branch-depth", type=int, default=28)
    parser.add_argument("--seed", type=Path)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    manifest, stage, accepted_stage, frontier, trace, candidate, runs = catalog.input_gate(args.catalog)
    accepted = json.loads((args.catalog / "VERIFIED.json").read_text())
    for name, digest in accepted["files"].items():
        if catalog.sha(args.catalog / name) != digest:
            raise ValueError("selected type discovery catalogue bytes changed")
    table = catalog.reconstruct(args.catalog, stage, accepted_stage, frontier, trace, candidate, runs)
    if table != json.loads((args.catalog / "CATALOG.json").read_text()):
        raise ValueError("selected type discovery did not replay catalogue")
    cap_report = json.loads((args.caps / "VERIFIED.json").read_text())
    for name, digest in cap_report["files"].items():
        if catalog.sha(args.caps / name) != digest:
            raise ValueError("selected type discovery cap bytes changed")
    cap = json.loads((args.caps / "CERTIFICATE.json").read_text())
    radius, arcs = F(cap["radius_upper"]), load_trig(args.caps)[0]
    caps, margins = cap_gate(radius, cap, arcs)
    seeds = {}
    if args.seed:
        previous = json.loads(args.seed.read_text())
        if (previous["catalog_acceptance_sha256"] != catalog.sha(args.catalog / "VERIFIED.json")
                or previous["cap_acceptance_sha256"] != catalog.sha(args.caps / "VERIFIED.json")
                or previous["radius_scope"] != "at-most-same-root-Rstar-not-original-U"):
            raise ValueError("selected type seed changed catalogue, caps or scope")
        seeds = {row["group_index"]: row for row in previous["proposals"]}
    proposals = []
    for group_index, group in enumerate(table["groups"]):
        if any(table["rows"][i]["same_canonical_type_as_known_candidate"] for i in group["member_indices"]):
            continue
        spec = {"N": 26, "B": group["B"], "next": 26, "faces": group["canonical_faces"]}
        matrix, derivation = constraint_matrix(spec, caps)
        if matrix is None:
            proposals.append({"group_index": group_index, "spec": spec, "sharp_domain_empty": True,
                              "derivation": derivation})
            continue
        seed = seeds.get(group_index)
        if seed:
            if seed["spec"] != spec or seed.get("sharp_domain_empty"):
                raise ValueError("selected type seed graph differs")
            nodes = seed["nodes"]
            previous_result, previous_pending, _ = replay(spec, matrix, radius, nodes, arcs)
            if not previous_pending:
                proposals.append(seed)
                continue
            stack = [(row["index"], list(map(F, row["lower"])), list(map(F, row["upper"])), 0)
                     for row in previous_pending]
        else:
            nodes = [{"kind": "OPEN"}]
            lower, upper = rootbox(matrix)
            stack = [(0, lower, upper, 0)]
        solver, checks = CorrelatedArcSolver(spec), 0
        while stack and checks < args.checks_per_type:
            index, lower, upper, depth = stack.pop()
            if depth > args.branch_depth:
                continue
            checks += 1
            box = tighten(matrix, lower, upper)
            if box is None:
                nodes[index] = {"kind": "EMPTY"}
                continue
            lower, upper = box
            node, status = solver.solve_correlated(lower, upper, matrix, radius)
            if node is not None:
                kind = "DIRECT_FORCE" if node["kind"] == "SHARP_FORCE" else "CORRELATED_FORCE"
                nodes[index] = {"kind": kind, "cert": node["cert"]}
            elif depth < args.branch_depth:
                influence = status["anchor_force_norm_proposal"]
                axis = max(range(spec["B"] - 1),
                           key=lambda i: float(upper[i] - lower[i]) * (influence[i] + 1e-12))
                middle = (lower[axis] + upper[axis]) / 2
                if lower[axis] < middle < upper[axis]:
                    children = [len(nodes), len(nodes) + 1]
                    nodes.extend(({"kind": "OPEN"}, {"kind": "OPEN"}))
                    nodes[index] = {"kind": "SPLIT", "axis": axis, "mid": str(middle), "children": children}
                    left_upper, right_lower = list(upper), list(lower)
                    left_upper[axis], right_lower[axis] = middle, middle
                    stack.extend(((children[0], list(lower), left_upper, depth + 1),
                                  (children[1], right_lower, list(upper), depth + 1)))
        result, pending, ledger = replay(spec, matrix, radius, nodes, arcs)
        proposals.append({"group_index": group_index, "spec": spec, "nodes": nodes, "checks": checks,
                          "replayed_discovery_counts": result, "pending": pending,
                          "independent_publication_and_source_type_acceptance_pending": True})
        print(json.dumps({"group_index": group_index, "verified": False, **result}), flush=True)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-selected-canonical-type-sharp-trees-v1", "verified": False,
        "catalog_acceptance_sha256": catalog.sha(args.catalog / "VERIFIED.json"),
        "cap_acceptance_sha256": catalog.sha(args.caps / "VERIFIED.json"),
        "radius_scope": "at-most-same-root-Rstar-not-original-U", "proposals": proposals,
        "all_unresolved_type_boxes_retained": True, "global_optimality_proved": False},
        separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
