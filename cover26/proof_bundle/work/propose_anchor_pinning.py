"""Rational discovery for a nonlocal anchor pinning certificate; not acceptance."""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import verify_anchor_pinning as pin


def nearest_integer(value):
    value = F(value)
    return (2 * value.numerator + value.denominator) // (2 * value.denominator)


def refine_cell(cell, relative, width):
    lo, hi = map(F, cell)
    while hi - lo > width:
        middle = (lo + hi) / 2
        cross = pin.geo.ivcross(pin.endpoint(middle), relative)
        if cross[0] > 0:
            lo = middle
        elif cross[1] < 0:
            hi = middle
        else:
            raise ValueError("angle refinement reached the exact-trig resolution")
    return [str(lo), str(hi)]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--local", type=Path, required=True)
    parser.add_argument("--transport", type=Path, required=True)
    parser.add_argument("--angle-width", default="1/10000000000000000000000000000")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    original, root, records, path_data, local, _ = pin.source_gate(args.stress, args.local, args.transport)
    geometry, edges, intervals, t = pin.root_geometry(original, root, records)
    width = F(args.angle_width)
    if not 0 < width <= F(1, 10**6):
        raise ValueError("invalid pinning discovery angle width")
    cells = [refine_cell(cell, geometry[i], width)
             for i, cell in enumerate(path_data["exact_rotated_anchor_cells"], 1)]
    scale = 10**60
    reference = [[str(nearest_integer((a + b) * scale / 2)) for a, b in point] for point in geometry]
    weights = [str(nearest_integer((a + b) * scale / 2)) for a, b in intervals]
    required = {frozenset(r["vertices"]) for r in records if r["kind"] == "face"}
    mapping = {int(k): v for k, v in path_data["native_to_exact_candidate_labels"].items()}
    rows = [row for row in path_data["states"] if row["next"] == 26
            and required <= {frozenset(mapping[i] for i in range(26) if mask >> i & 1)
                             for mask in row["faces"]}]
    support = min(rows, key=lambda row: len(row["prefix"]))
    proposal = {
        "schema": "N26-rational-nonlocal-anchor-pinning-proposal-v1",
        "verified": False, "N": 26, "B": 16,
        "radius_scope": "at-most-the-certified-same-root-Rstar",
        "source_acceptance_sha256": {
            "stress": pin.sha(args.stress / "VERIFIED.json"),
            "local": pin.sha(args.local / "VERIFIED.json"),
            "transport": pin.sha(args.transport / "VERIFIED.json"),
        },
        "minimum_positive_support_prefix": support["prefix"],
        "closed_anchor_angle_cells": cells,
        "rational_scale": str(scale), "edges": [list(e) for e in edges],
        "reference_numerators": reference, "weight_numerators": weights,
        "global_optimality_proved": False,
    }
    args.output.write_text(json.dumps(proposal, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "minimum_positive_support_prefix": support["prefix"],
                      "paid_faces": len(support["faces"]), "positive_rods": len(edges),
                      "angle_width_target": str(width), "global_optimality_proved": False}), flush=True)


if __name__ == "__main__":
    main()
