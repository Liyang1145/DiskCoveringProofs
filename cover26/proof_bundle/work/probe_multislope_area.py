"""Floating LP proposals combining area envelopes with graph angle constraints.

No floating result from this file is an accepted exclusion certificate.
"""

from collections import deque
from fractions import Fraction as F
import json
from math import asin, pi
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

from verify_degree_area import U, sha


WORK = Path(__file__).resolve().parent
FOLDER = WORK.parent / "outputs/n26-degree-area-lower-v1"
SLOPES = [F(q, 4) for q in (-12, -16, -18, -20, -21, -22, -23, -24,
                            -25, -26, -28, -32, -40, -48, -64, -96)]
CAPS = (754112, 1555305, 2486507, 3880649)
ANGLE_SCALE = 10**7


def adjacency_of(faces):
    adjacency = [set() for _ in range(26)]
    for mask in faces:
        vertices = [i for i in range(26) if mask >> i & 1]
        for i in vertices:
            adjacency[i].update(j for j in vertices if j != i)
    return adjacency


def angle_rows(b, adjacency):
    distances = []
    for start in range(b):
        ds = [27] * 26
        ds[start] = 0
        pending = deque([start])
        while pending:
            i = pending.popleft()
            if ds[i] == 3:
                continue
            for j in adjacency[i]:
                if ds[j] > ds[i] + 1:
                    ds[j] = ds[i] + 1
                    pending.append(j)
        distances.append(ds)
    result = set()
    for i in range(b):
        for j in range(i + 1, b):
            d = min(distances[u][v] for u in (i, (i + 1) % b)
                    for v in (j, (j + 1) % b))
            if d > 3:
                continue
            cap = CAPS[max(1, d)]
            k = j - i
            if min(k, b - k) * CAPS[0] <= cap:
                continue
            forward = k * CAPS[0] < ANGLE_SCALE - cap
            backward = (b - k) * CAPS[0] < ANGLE_SCALE - cap
            if forward and backward:
                raise ValueError("source graph fails its necessary angle screen")
            mask = sum(1 << v for v in range(i + 1, j + 1))
            if forward:
                result.add((mask, cap))
            elif backward:
                result.add((((1 << b) - 1) ^ mask, cap))
    return tuple(sorted(result))


def numeric_intercepts():
    r = float(U)
    t = r * r
    x = np.linspace(0, asin(r) / pi, 16385)
    beta = np.arcsin(np.minimum(1, np.sin(pi * x) / r))
    table = []
    for d in range(2, 26):
        regular = .5 * t * (d + 1) * np.sin(2 * pi / (d + 1))
        active = (2 * np.sin(pi * x) > r) & (beta >= pi / (d + 1))
        special = .5 * t * (np.sin(2 * beta) + d * np.sin((2 * pi - 2 * beta) / d))
        h = np.where(active, special, regular) - .5 * np.sin(2 * pi * x)
        table.append([float(np.max(h - float(slope) * x)) for slope in SLOPES])
    return table


def solve_boundary(b, degrees, angle_constraints, table):
    rows, rhs = [], []
    for i, d in enumerate(degrees):
        for j, slope in enumerate(SLOPES):
            row = np.zeros(2 * b)
            row[i] = -float(slope)
            row[b + i] = 1
            rows.append(row)
            rhs.append(table[d - 2][j])
    for mask, cap in angle_constraints:
        rows.append(np.array([float(mask >> i & 1) for i in range(b)] + [0.] * b))
        rhs.append(cap / ANGLE_SCALE)
    for sign in (1, -1):
        for i in range(b):
            row = np.zeros(2 * b)
            row[i] = sign
            rows.append(row)
            rhs.append(CAPS[0] / ANGLE_SCALE if sign == 1 else 0.)
    run = linprog(np.r_[np.zeros(b), -np.ones(b)], A_ub=np.array(rows), b_ub=np.array(rhs),
                  A_eq=np.array([np.r_[np.ones(b), np.zeros(b)]]), b_eq=[1.],
                  bounds=[(None, None)] * (2 * b), method="highs")
    if not run.success:
        raise ValueError("unexpected floating LP failure: " + run.message)
    weights = -run.ineqlin.marginals
    return {
        "B": b, "boundary_degrees": list(degrees),
        "angle_constraints": [list(row) for row in angle_constraints],
        "floating_boundary_upper_proposal": float(-run.fun),
        "dual_nonzero_proposals": [[i, float(w)] for i, w in enumerate(weights) if w > 1e-12],
        "primal_gaps_proposal": run.x[:b].tolist(),
    }


def main():
    output = WORK / "n26-multislope-area-proposals-v1.json"
    if output.exists():
        raise FileExistsError(output)
    graphs = json.loads((FOLDER / "GRAPH-LEDGER.json").read_text())
    profiles = json.loads((FOLDER / "PROFILE-LEDGER.json").read_text())
    cert = json.loads((FOLDER / "CERTIFICATE.json").read_text())
    table = numeric_intercepts()
    cases, case_ids, mappings = [], {}, []
    proposed = new_proposed = 0
    minimum = None
    for index, (b, faces, profile_id) in enumerate(graphs):
        adjacency = adjacency_of(faces)
        degrees = tuple(len(adjacency[i]) for i in range(b))
        constraints = angle_rows(b, adjacency)
        key = (b, degrees, constraints)
        if key not in case_ids:
            case_ids[key] = len(cases)
            cases.append(solve_boundary(b, degrees, constraints, table))
        case_id = case_ids[key]
        interior = profiles[profile_id]["interior_degree_counts_d2_to_d25"]
        area = sum(c * n for c, n in zip(cert["interior_area_upper_integers"], interior)) / 10**12
        value = area + cases[case_id]["floating_boundary_upper_proposal"]
        minimum = value if minimum is None else min(minimum, value)
        is_old = profiles[profile_id]["strictly_excluded_as_cover_transport_type"]
        if value < -1e-7:
            proposed += 1
            new_proposed += not is_old
        mappings.append(case_id)
        if (index + 1) % 1000 == 0:
            print(json.dumps({"graphs_probed": index + 1, "LP_cases": len(cases),
                              "proposed_exclusions": proposed, "new_proposed_exclusions": new_proposed}),
                  flush=True)
    result = {"verified": False, "slopes": list(map(str, SLOPES)),
              "source_graph_ledger_sha256": sha(FOLDER / "GRAPH-LEDGER.json"),
              "source_profile_ledger_sha256": sha(FOLDER / "PROFILE-LEDGER.json"),
              "cases": cases, "graph_to_case": mappings,
              "floating_proposed_exclusions": proposed,
              "floating_new_proposed_exclusions": new_proposed,
              "global_optimality_proved": False}
    output.write_text(json.dumps(result, separators=(",", ":")) + "\n")
    print(json.dumps({"verified": False, "graphs": len(graphs), "LP_cases": len(cases),
                      "proposed_exclusions": proposed, "new_proposed_exclusions": new_proposed,
                      "minimum_float_dual": minimum}), flush=True)


if __name__ == "__main__":
    main()
