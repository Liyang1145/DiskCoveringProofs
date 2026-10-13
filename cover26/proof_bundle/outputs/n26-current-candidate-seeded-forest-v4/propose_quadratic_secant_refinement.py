"""Unaccepted coordinatewise curvature and exact secant/dual energy refinements."""

import argparse
from fractions import Fraction as F
import json
from math import ceil
from pathlib import Path

import numpy as np
from scipy.optimize import linprog, minimize

from n26_force import load_trig
from n26_sharp_radius_constraints import SCALE
import n26_quadratic_energy_minorant as exact
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import sha


def dual(kernel, matrix, ref, lo, hi, gradient, diagonal, mode):
    shifted = list(gradient)
    if mode == "box-secant":
        for k, allowance in enumerate(diagonal, 1):
            slope = allowance * (lo[k] + hi[k] - 2 * ref[k]) / 2
            shifted[k] = tuple(g - slope for g in gradient[k])
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
    objective = [float((a + c) / 2) for a, c in shifted[1:]]
    lp = linprog(objective, A_ub=rows, b_ub=rhs,
                 bounds=[(float(a), float(c)) for a, c in zip(lo[1:], hi[1:])], method="highs")
    q, terms = 10**30, []
    if lp.success:
        for (i, j), value in zip(pairs, lp.ineqlin.marginals):
            numerator = max(0, round(-float(value) * q))
            if numerator:
                terms.append([i, j, str(numerator)])
    return {"q": q, "terms": terms}


def refine(kernel, matrix, box, previous, radius, arcs):
    lo, hi = box["lower"], box["upper"]
    reference = previous["reference_turns"]
    ref, lower, upper = exact.reference_gate(reference, lo, hi, matrix)
    hessian = exact.hessian_minorant(kernel, matrix, lo, hi, arcs)
    h = np.array([[float(x) for x in row] for row in hessian])
    widths = [max(abs(a - x), abs(c - x), F(1, 10**10))
              for a, c, x in zip(lower[1:], upper[1:], ref[1:])]
    width = np.array(list(map(float, widths)))
    transformed = h * width[:, None] * width[None, :]
    minimum = float(np.linalg.eigvalsh(transformed)[0])
    weighted_eta = F(ceil(max(0., -minimum + 1e-12) * 10**12), 10**12)
    weighted = [weighted_eta / x**2 for x in widths]
    scalar = list(map(F, previous["eta"])) if isinstance(previous["eta"], list) else [
        F(previous["eta"])] * len(widths)
    start = np.array(list(map(float, weighted)))
    costs = width**2 / max(width**2)

    def spectral(values):
        eigenvalues, eigenvectors = np.linalg.eigh(h + np.diag(values))
        return float(eigenvalues[0]) - 1e-9, eigenvectors[:, 0]**2

    result = minimize(lambda x: float(costs @ x), start, jac=lambda x: costs,
                      bounds=[(0., None)] * len(start),
                      constraints={"type": "ineq", "fun": lambda x: spectral(x)[0],
                                   "jac": lambda x: spectral(x)[1]},
                      method="SLSQP", options={"ftol": 1e-12, "maxiter": 200, "disp": False})
    optimized = [F(ceil(max(0., float(x) + 1e-8) * 10**10), 10**10) for x in result.x]
    _, gradient = exact.point_energy_gradient(kernel, ref, arcs)
    candidates = []
    for label, diagonal in (("scalar", scalar), ("width-normalized", weighted), ("optimized-diagonal", optimized)):
        for attempt in range(6):
            try:
                exact.curvature_gate(kernel, matrix, lo, hi, diagonal, arcs)
            except ValueError:
                diagonal = [x * F(101, 100) + F(1, 10**8) for x in diagonal]
            else:
                break
        else:
            continue
        for mode in ("constant-max-square", "box-secant"):
            cert = {"reference_turns": reference, "eta": list(map(str, diagonal)),
                    "curvature_mode": mode,
                    "difference_dual": dual(kernel, matrix, ref, lower, upper, gradient, diagonal, mode)}
            check = exact.bound(kernel, matrix, lo, hi, cert, radius, arcs)
            candidates.append((cert, check, label))
    if not candidates:
        raise ValueError("no exactly verified curvature diagonal survived")
    return max(candidates, key=lambda row: F(row[1]["minimum_strict_energy_margin"]))


def main():
    parser = argparse.ArgumentParser()
    for key in ("registry", "registry-replay", "seed", "kernels", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    accepted, _ = bound(args.registry)
    if read(args.registry_replay) != accepted:
        raise ValueError("secant refinement lacks actual accepted source replay")
    seed, kernels = read(args.seed), read(args.kernels)
    if (seed["registry_acceptance_sha256"] != sha(args.registry / "VERIFIED.json")
            or seed["kernels_sha256"] != sha(args.kernels)):
        raise ValueError("secant refinement changed source graph or kernel")
    domains = {row["group_index"]: row["matrix"] for row in read(args.registry / "DOMAINS.json")}
    pending = {group["group_index"]: {row["index"]: row for row in group["closed_OPEN_boxes"]}
               for group in read(args.registry / "PENDING-TYPES.json")}
    radius, arcs = F(accepted["radius_upper"]), load_trig(args.registry)[0]
    exact_kernels = [exact.kernel_gate(row["certificate"]["spec"], row["certificate"]) for row in kernels]
    proposals, paid = [], 0
    for row in seed["proposals"]:
        index, source_index = row["group_index"], row["source_OPEN_index"]
        kernel = exact_kernels[row["kernel_index"]]
        cert, check, method = refine(kernel, domains[index], pending[index][source_index],
                                     row["certificate"], radius, arcs)
        if check["radius_at_most_Rstar_whole_box_excluded"]:
            paid += 1
        proposals.append({**row, "certificate": cert, "discovery_exact_result": check,
                          "chosen_discovery_curvature_strategy": method})
        print(json.dumps({"verified": False, "group_index": index, "OPEN_index": source_index,
                          "strict_whole_box_energy_proposed": check["radius_at_most_Rstar_whole_box_excluded"],
                          "mode": cert["curvature_mode"], "strategy": method,
                          "exact_energy_margin_for_discovery": float(F(check["minimum_strict_energy_margin"]))}),
              flush=True)
    args.output.write_text(json.dumps({
        **{key: value for key, value in seed.items() if key not in ("proposals", "strict_whole_box_proposals")},
        "proposals": proposals, "strict_whole_box_proposals": paid,
        "seed_sha256": sha(args.seed), "independent_standalone_acceptance_still_required": True},
        separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
