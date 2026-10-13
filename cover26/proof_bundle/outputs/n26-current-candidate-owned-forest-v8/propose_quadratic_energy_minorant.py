"""Unaccepted exact negative-curvature energy proposals on current type OPEN."""

import argparse
from fractions import Fraction as F
import json
from math import ceil
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from sympy import Matrix

from n26_force import load_trig, rod_graph
from n26_sharp_radius_constraints import SCALE, tighten
import n26_quadratic_energy_minorant as exact
from verify_selected_type_trees import SCOPE, bound, read
from verify_terminal_catalog import sha


def make_kernel(spec, raw_weights):
    vertices, edges = rod_graph(spec)
    b, q = spec["B"], 10**18
    weights = [max(1, round(float(w) * q)) for w in raw_weights]
    if len(weights) != len(edges):
        raise ValueError("quadratic discovery weight dimension differs from its full graph")
    lap = [[0] * vertices for _ in range(vertices)]
    for (u, v), weight in zip(edges, weights):
        lap[u][u] += weight
        lap[v][v] += weight
        lap[u][v] -= weight
        lap[v][u] -= weight
    inverse, denominator = Matrix([row[b:] for row in lap[b:]]).to_DM().inv_den()
    nums, den = [[int(x) for x in row] for row in inverse.to_Matrix().tolist()], int(denominator)
    if den < 0:
        nums, den = [[-x for x in row] for row in nums], -den
    certificate = {
        "schema": "N26-full-type-positive-quadratic-ground-kernel-v1", "spec": spec,
        "weight_scale": q, "weight_numerators": weights,
        "inverse_denominator": str(den), "inverse_numerators": [[str(x) for x in row] for row in nums]}
    kernel = exact.kernel_gate(spec, certificate)
    return certificate, kernel


def rational_reference(angles, lower, upper, matrix):
    lo, hi = list(map(F, lower)), list(map(F, upper))
    candidate = [max(a, min(c, F(round(float(x) * 10**12), 10**12) - F(1, 10**8)))
                 for x, a, c in zip(angles, lo, hi)]
    projected = tighten(matrix, candidate, hi)
    if projected is not None:
        reference = projected[0]
        try:
            exact.reference_gate(reference, lo, hi, matrix)
        except ValueError:
            pass
        else:
            return list(map(str, reference))
    reference = [(a + c) / 2 for a, c in zip(lo, hi)]
    exact.reference_gate(reference, lo, hi, matrix)
    return list(map(str, reference))


def payment(kernel, matrix, box, angles, radius, arcs):
    lower, upper = box["lower"], box["upper"]
    reference = rational_reference(angles, lower, upper, matrix)
    hessian = exact.hessian_minorant(kernel, matrix, lower, upper, arcs)
    minimum = float(np.linalg.eigvalsh(np.array([[float(x) for x in row] for row in hessian]))[0])
    eta = F(ceil(max(0., -minimum + 1e-8) * 10**8), 10**8)
    for attempt in range(5):
        try:
            exact.curvature_gate(kernel, matrix, lower, upper, eta, arcs)
        except ValueError:
            eta = eta * F(101, 100) + F(1, 10**8)
        else:
            break
    else:
        raise ValueError("proposed curvature allowance could not be certified")
    ref, lo, hi = exact.reference_gate(reference, lower, upper, matrix)
    _, gradient = exact.point_energy_gradient(kernel, ref, arcs)
    rows, rhs, pairs = [], [], []
    for i in range(kernel["B"]):
        for j in range(kernel["B"]):
            if i == j:
                continue
            row = [0] * (kernel["B"] - 1)
            if i:
                row[i - 1] -= 1
            if j:
                row[j - 1] += 1
            rows.append(row)
            rhs.append(float(F(matrix[i][j], SCALE)))
            pairs.append((i, j))
    objective = [float((a + c) / 2) for a, c in gradient[1:]]
    lp = linprog(objective, A_ub=rows, b_ub=rhs,
                 bounds=[(float(a), float(c)) for a, c in zip(lo[1:], hi[1:])], method="highs")
    q, terms = 10**30, []
    if lp.success:
        for (i, j), value in zip(pairs, lp.ineqlin.marginals):
            numerator = max(0, round(-float(value) * q))
            if numerator:
                terms.append([i, j, str(numerator)])
    certificate = {"reference_turns": reference, "eta": str(eta),
                   "difference_dual": {"q": q, "terms": terms}}
    result = exact.bound(kernel, matrix, lower, upper, certificate, radius, arcs)
    return certificate, result


def main():
    parser = argparse.ArgumentParser()
    for key in ("registry", "registry-replay", "diagnostics", "output", "kernels-output"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--only-groups", type=int, nargs="+")
    args = parser.parse_args()
    if args.output.exists() or args.kernels_output.exists():
        raise FileExistsError("fresh quadratic discovery paths required")
    accepted, _ = bound(args.registry)
    if read(args.registry_replay) != accepted or accepted["radius_scope"] != SCOPE:
        raise ValueError("quadratic discovery source lacks its actual Rstar replay")
    diagnostics = read(args.diagnostics)
    records = {row["group_index"]: row for row in diagnostics["results"]}
    domains = {row["group_index"]: row["matrix"] for row in read(args.registry / "DOMAINS.json")}
    radius, arcs = F(accepted["radius_upper"]), load_trig(args.registry)[0]
    kernels, proposals, paid, checked = [], [], 0, 0
    for group in read(args.registry / "PENDING-TYPES.json"):
        index = group["group_index"]
        if (not group["closed_OPEN_boxes"] or (args.only_groups and index not in args.only_groups)
                or index not in records):
            continue
        numerical = records[index]
        certificate, kernel = make_kernel(group["spec"], numerical["floating_weights"])
        kernel_index = len(kernels)
        kernels.append({"group_index": index, "certificate": certificate})
        for box in group["closed_OPEN_boxes"]:
            cert, result = payment(kernel, domains[index], box,
                                   numerical["floating_stationary_angles"], radius, arcs)
            checked += 1
            if result["radius_at_most_Rstar_whole_box_excluded"]:
                paid += 1
            proposals.append({"group_index": index, "source_OPEN_index": box["index"],
                              "kernel_index": kernel_index, "certificate": cert, "discovery_exact_result": result})
            print(json.dumps({"verified": False, "group_index": index, "OPEN_index": box["index"],
                              "whole_box_proposed_paid": result["radius_at_most_Rstar_whole_box_excluded"],
                              "exact_negative_curvature_allowance": cert["eta"],
                              "exact_energy_margin_for_discovery": float(F(result["minimum_strict_energy_margin"]))}),
                  flush=True)
    args.kernels_output.write_text(json.dumps(kernels, separators=(",", ":")) + "\n", encoding="utf-8")
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-full-type-quadratic-negative-curvature-payments-v1",
        "verified": False, "radius_scope": SCOPE,
        "registry_acceptance_sha256": sha(args.registry / "VERIFIED.json"),
        "kernels_sha256": sha(args.kernels_output), "diagnostics_sha256": sha(args.diagnostics),
        "proposals": proposals, "source_OPEN_boxes_checked": checked, "strict_whole_box_proposals": paid,
        "all_numerical_objectives_and_eigenvalues_not_used_as_proof": True,
        "independent_source_partition_and_standalone_acceptance_still_required": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "boxes_checked": checked, "strict_whole_box_proposals": paid}), flush=True)


if __name__ == "__main__":
    main()
