"""Floating partial-subtree LP proposals; never an acceptance path."""

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

from audit_area_prefix_envelopes import completion_degree_bounds
from audit_prefix_origin import OriginReference
from new_upper_scope import local_path
from probe_multislope_area import ANGLE_SCALE, CAPS, SLOPES, angle_rows, numeric_intercepts


WORK = Path(__file__).resolve().parent


def solve_state(b, state, intercepts, interior_coefficients):
    bounds = completion_degree_bounds(26, b, state)
    if bounds is None:
        return {"degree_domain_empty": True}
    adjacency = [{j for j in range(26) if mask >> j & 1} for mask in state["adjacency"]]
    angles = angle_rows(b, adjacency)
    zs = [(i, d) for i, (lo, hi) in enumerate(bounds) for d in range(lo, hi + 1)]
    dimension = 2 * b + len(zs)
    z_indices = [{d: 2 * b + index for index, (owner, d) in enumerate(zs) if owner == i}
                 for i in range(26)]
    objective = np.zeros(dimension)
    objective[b:2 * b] = -1
    for i in range(b, 26):
        for d, index in z_indices[i].items():
            objective[index] = -interior_coefficients[d - 2]
    rows, rhs = [], []
    for i in range(b):
        for j, slope in enumerate(SLOPES):
            row = np.zeros(dimension)
            row[i] = -float(slope)
            row[b + i] = 1
            for d, index in z_indices[i].items():
                row[index] = -intercepts[d - 2][j]
            rows.append(row)
            rhs.append(0.)
    for mask, cap in angles:
        row = np.zeros(dimension)
        for i in range(b):
            row[i] = mask >> i & 1
        rows.append(row)
        rhs.append(cap / ANGLE_SCALE)
    for sign in (1, -1):
        for i in range(b):
            row = np.zeros(dimension)
            row[i] = sign
            rows.append(row)
            rhs.append(CAPS[0] / ANGLE_SCALE if sign == 1 else 0.)
    equalities, eq_rhs = [], []
    row = np.zeros(dimension)
    row[:b] = 1
    equalities.append(row)
    eq_rhs.append(1.)
    for i in range(26):
        row = np.zeros(dimension)
        for index in z_indices[i].values():
            row[index] = 1
        equalities.append(row)
        eq_rhs.append(1.)
    row = np.zeros(dimension)
    for index, (i, d) in enumerate(zs, 2 * b):
        row[index] = d
    equalities.append(row)
    eq_rhs.append(150 - 2 * b)
    result = linprog(objective, A_ub=np.array(rows), b_ub=np.array(rhs),
                     A_eq=np.array(equalities), b_eq=np.array(eq_rhs),
                     bounds=[(None, None)] * (2 * b) + [(0., None)] * len(zs),
                     method="highs")
    if not result.success:
        return {"floating_LP_success": False, "message": result.message}
    return {
        "floating_LP_success": True, "degree_bounds": [list(pair) for pair in bounds],
        "angle_constraints": [list(pair) for pair in angles],
        "floating_area_upper_proposal": float(-result.fun),
        "degree_equality_multiplier_proposal": float(result.eqlin.marginals[-1]),
        "dual_nonzero_proposals": [[i, float(-w)] for i, w in enumerate(result.ineqlin.marginals) if -w > 1e-12],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--b", type=int, choices=(14, 15, 16, 17), default=14)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--all-ancestors", action="store_true")
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    b = args.b
    scope = WORK.parent / "outputs/n26-new-scope-v1/CONSTANTS.json"
    constants = json.loads(scope.read_text())
    reference = OriginReference(26, b, "dfs", caps=constants["angle_caps"], scale=constants["angle_scale"])
    frontier = json.loads((WORK.parent / f"outputs/n26-new-scope-frontiers-v1/N26-B{b}-frontier.json").read_text())
    prefixes = {(), *(tuple(row["prefix"]) for row in frontier["frontier"])}
    if args.all_ancestors:
        progress = json.loads((WORK.parent / f"outputs/n26-new-B{b}-progress-v1.json").read_text())
        manifest = json.loads(local_path(progress["latest_checkpoint"]).read_text())
        for p in manifest["pending_prefixes"] + manifest["closed_prefixes"]:
            for length in range(len(p) + 1):
                prefixes.add(tuple(p[:length]))
    intercepts = numeric_intercepts()
    cert = json.loads((WORK.parent / "outputs/n26-degree-area-lower-v1/CERTIFICATE.json").read_text())
    interior = np.array(cert["interior_area_upper_integers"]) / 10**12
    rows = []
    for prefix in sorted(prefixes, key=lambda p: (len(p), p)):
        state = reference.resolve(prefix)
        descriptor = reference.entry(prefix, state, reference.children(state))
        result = solve_state(b, descriptor, intercepts, interior)
        rows.append({"B": b, "prefix": list(prefix), **result})
        print(json.dumps({key: value for key, value in rows[-1].items() if key in
                          ("B", "prefix", "floating_LP_success", "floating_area_upper_proposal",
                           "degree_domain_empty", "message")}), flush=True)
    args.output.write_text(json.dumps({"verified": False, "B": b, "rows": rows,
                                       "global_optimality_proved": False}, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
