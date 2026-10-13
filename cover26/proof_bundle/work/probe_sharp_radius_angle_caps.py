"""Discovery-only stricter necessary angle domains at the certified root.

No queue is edited. Proposed negative cycles and empty angle boxes remain
unaccepted until a separate source-bound proof/interface replay is published.
"""

import argparse
from collections import deque
from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import load_trig, spec_gate
from new_upper_scope import sha
from propose_anchor_pinning import refine_cell
import verify_anchor_pinning as geometry


def caps_for(radius_upper, digits, arcs):
    scale = 10**digits
    caps, margins = [], []
    for k in range(1, 5):
        lo, hi = 0, scale // 2
        while hi - lo > 1:
            mid = (lo + hi) // 2
            lower = F(arcs.sincos_turn(F(mid, 2 * scale))[1][0], arcs.SCALE)
            if lower > k * radius_upper:
                hi = mid
            else:
                lo = mid
        margin = F(arcs.sincos_turn(F(hi, 2 * scale))[1][0], arcs.SCALE) - k * radius_upper
        if margin <= 0:
            raise ValueError("sharp sine cap not outward certified")
        caps.append(hi)
        margins.append(margin)
    if not 0 < caps[0] < caps[1] < caps[2] < caps[3] < scale // 2:
        raise ValueError("invalid sharp root angle caps")
    return scale, caps, margins


def domain(spec, caps, scale):
    b, next_vertex, faces, adjacency = spec_gate(spec)
    matrix = [[2 * scale] * b for _ in range(b)]
    for i in range(b):
        matrix[i][i] = 0
        j = (i + 1) % b
        matrix[i][j] = caps[0] - (scale if j == 0 else 0)
        matrix[j][i] = scale if j == 0 else 0
    for i in range(b):
        distances = [next_vertex + 1] * next_vertex
        pending = deque((i, (i + 1) % b))
        for v in pending:
            distances[v] = 0
        while pending:
            v = pending.popleft()
            if distances[v] == 3:
                continue
            for w in range(next_vertex):
                if adjacency[v] >> w & 1 and distances[w] > distances[v] + 1:
                    distances[w] = distances[v] + 1
                    pending.append(w)
        for j in range(i + 1, b):
            h = min(distances[j], distances[(j + 1) % b])
            if h > 3:
                continue
            cap, k = caps[h], j - i
            if min(k, b - k) * caps[0] <= cap:
                continue
            forward = k * caps[0] < scale - cap
            backward = (b - k) * caps[0] < scale - cap
            if forward and backward:
                return None, "opposite-forced-short-arcs"
            if forward:
                matrix[i][j] = min(matrix[i][j], cap)
            elif backward:
                matrix[j][i] = min(matrix[j][i], cap - scale)
    for k in range(b):
        for i in range(b):
            for j in range(b):
                matrix[i][j] = min(matrix[i][j], matrix[i][k] + matrix[k][j])
    if any(matrix[i][i] < 0 for i in range(b)):
        return None, "negative-difference-cycle"
    return matrix, None


def tighten(matrix, scale, lower, upper):
    b = len(matrix)
    lo, hi = [F(0), *map(F, lower)], [F(0), *map(F, upper)]
    if len(lo) != b or len(hi) != b or any(a > c for a, c in zip(lo, hi)):
        raise ValueError("invalid sharp-angle trial box")
    new_lo = [max(lo[i] - F(matrix[j][i], scale) for i in range(b)) for j in range(b)]
    new_hi = [min(hi[i] + F(matrix[i][j], scale) for i in range(b)) for j in range(b)]
    return None if any(a > c for a, c in zip(new_lo, new_hi)) else (new_lo[1:], new_hi[1:])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--local", type=Path, required=True)
    parser.add_argument("--transport", type=Path, required=True)
    parser.add_argument("--frontier", type=Path, required=True)
    parser.add_argument("--acceptance", type=Path, required=True)
    parser.add_argument("--angles", type=Path, required=True)
    parser.add_argument("--digits", type=int, default=40)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    if not 30 <= args.digits <= 44:
        raise ValueError("unsupported discovery cap scale")
    accepted = json.loads(args.acceptance.read_text())
    if not accepted["verified"] or accepted["files"]["FRONTIER.json"] != sha(args.frontier):
        raise ValueError("global discovery frontier not bound")
    stress_report = json.loads((args.stress / "VERIFIED.json").read_text())
    radius_upper = F(stress_report["modified_root_check"]["r_strict_interval"][1])
    arcs = load_trig()[0]
    scale, caps, margins = caps_for(radius_upper, args.digits, arcs)
    frontier = json.loads(args.frontier.read_text())
    proposed = []
    for row in frontier["pending_states"]:
        spec = {"N": 26, "B": row["B"], "next": row["next"], "faces": row["faces"]}
        matrix, reason = domain(spec, caps, scale)
        if matrix is None:
            proposed.append({"B": row["B"], "prefix": row["prefix"], "reason": reason})
    original, root, records, path_data, local, inventory = geometry.source_gate(
        args.stress, args.local, args.transport)
    rotated, edges, weights, t = geometry.root_geometry(original, root, records)
    final = path_data["states"][-1]
    spec = {"N": 26, "B": 16, "next": 26, "faces": final["faces"]}
    matrix, reason = domain(spec, caps, scale)
    if matrix is None:
        raise AssertionError("known same-root covering graph lost by sharp caps")
    tiny = [refine_cell(cell, rotated[i], F(1, 10**45))
            for i, cell in enumerate(path_data["exact_rotated_anchor_cells"], 1)]
    angular = [(F(0), F(0)), *[tuple(map(F, cell)) for cell in tiny]]
    if any(angular[j][1] - angular[i][0] > F(matrix[i][j], scale)
           for i in range(16) for j in range(16) if i != j):
        raise ValueError("known candidate tiny cells not certified within all sharp constraints")
    angle_report, _ = geometry.checked_bundle(args.angles)
    pending = json.loads((args.angles / "PENDING-ANGLES.json").read_text())
    empty = [row["index"] for row in pending if tighten(matrix, scale, row["lower"], row["upper"]) is None]
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-sharp-root-angle-cap-discovery-v1",
        "verified": False, "N": 26, "radius_scope": "same-root-Rstar",
        "radius_upper": str(radius_upper), "scale": str(scale), "caps": list(map(str, caps)),
        "strict_sine_margins": list(map(str, margins)),
        "source_stress_acceptance_sha256": sha(args.stress / "VERIFIED.json"),
        "source_frontier_sha256": sha(args.frontier),
        "source_frontier_acceptance_sha256": sha(args.acceptance),
        "source_angle_acceptance_sha256": sha(args.angles / "VERIFIED.json"),
        "known_candidate_tiny_angle_cells": tiny,
        "proposed_negative_cycle_subtrees": proposed,
        "proposed_empty_candidate_OPEN_indices": empty,
        "independent_interface_and_publication_acceptance_pending": True,
        "global_optimality_proved": False,
    }, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "verified": False, "sharp_cap_digits": args.digits,
        "pending_subtrees_tested": len(frontier["pending_states"]),
        "proposed_negative_cycle_subtrees": len(proposed),
        "candidate_OPEN_boxes_tested": len(pending),
        "proposed_empty_candidate_OPEN_boxes": len(empty),
        "known_exact_candidate_survives_full_sharp_constraints": True,
    }), flush=True)


if __name__ == "__main__":
    main()
