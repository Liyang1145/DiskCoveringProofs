"""Numerical discovery for full Dirichlet center pinning; not a certificate."""

import argparse
from fractions import Fraction as F
import json
from math import pi
from pathlib import Path

import numpy as np

from verify_selected_type_trees import bound, read
from verify_terminal_catalog import sha


def main():
    parser = argparse.ArgumentParser()
    for key in ("source", "pinning", "caps", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    for folder in (args.source, args.pinning, args.caps):
        bound(folder)
    proposal = read(args.pinning / "CERTIFICATE.json")
    cap = read(args.caps / "CERTIFICATE.json")
    source = read(args.source / "CERTIFICATE.json")
    if source["spec"]["B"] != 16:
        raise ValueError("Dirichlet discovery is for the accepted full candidate only")
    scale = int(proposal["rational_scale"])
    points = np.array([[float(F(int(n), scale)) for n in row] for row in proposal["reference_numerators"]])
    weights = np.array([float(F(int(n), scale)) for n in proposal["weight_numerators"]])
    lap = np.zeros((62, 62))
    for (u, v), w in zip(proposal["edges"], weights):
        lap[u, u] += w
        lap[v, v] += w
        lap[u, v] -= w
        lap[v, u] -= w
    inverse = np.linalg.inv(lap[16:, 16:])
    harmonic = -inverse @ lap[16:, :16]
    schur = lap[:16, :16] + lap[:16, 16:] @ harmonic
    energy_upper = float(F(cap["radius_upper"]))**2 * sum(weights)
    pair_weights = -np.triu(schur, 1)
    i, j = np.where(pair_weights > 0)
    w = pair_weights[i, j]
    results = []
    for row in read(args.source / "PENDING-ANGLES.json"):
        lo, hi = np.array([0., *map(lambda x: float(F(x)), row["sharp_lower"])]), np.array(
            [0., *map(lambda x: float(F(x)), row["sharp_upper"])])
        middle, halfwidth = (lo + hi) / 2, (hi - lo) / 2
        angles = 2 * pi * middle
        anchors = np.c_[np.cos(angles), np.sin(angles)]
        delta = angles[j] - angles[i]
        e0 = 2 * np.dot(w, 1 - np.cos(delta))
        gradient = np.zeros(16)
        np.add.at(gradient, i, -4 * pi * w * np.sin(delta))
        np.add.at(gradient, j, 4 * pi * w * np.sin(delta))
        lower = e0 - np.dot(np.abs(gradient), halfwidth) - 4 * pi**2 * np.dot(
            w, (halfwidth[i] + halfwidth[j])**2)
        slack = energy_upper - lower
        mean = harmonic @ anchors
        error = np.linalg.norm(mean[:26] - points[16:42], axis=1)
        error += (harmonic @ (2 * pi * halfwidth))[:26]
        error += np.sqrt(np.diag(inverse)[:26] * max(slack, 0))
        results.append({"index": row["index"], "floating_energy_slack": float(slack),
                        "floating_maximum_center_error": float(max(error)),
                        "proposed_enters_unchanged_local_allowance": bool(max(error) < 7 / 800000)})
    report = {
        "schema": "N26-unaccepted-Dirichlet-candidate-entry-diagnostics-v1", "verified": False,
        "source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
        "pinning_acceptance_sha256": sha(args.pinning / "VERIFIED.json"),
        "cap_acceptance_sha256": sha(args.caps / "VERIFIED.json"),
        "minimum_floating_harmonic_coefficient": float(np.min(harmonic)),
        "maximum_floating_row_sum_residual": float(np.max(np.abs(harmonic.sum(axis=1) - 1))),
        "results": results, "all_bounds_are_discovery_only": True,
        "exact_integer_Kron_elimination_and_Taylor_enclosures_required": True,
        "global_optimality_proved": False}
    args.output.write_text(json.dumps(report, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "boxes": len(results),
                      "proposed_LOCAL": sum(row["proposed_enters_unchanged_local_allowance"] for row in results),
                      "proposed_negative_energy_slack": sum(row["floating_energy_slack"] < -1e-15 for row in results),
                      "minimum_error": min(row["floating_maximum_center_error"] for row in results),
                      "maximum_error": max(row["floating_maximum_center_error"] for row in results)}), flush=True)


if __name__ == "__main__":
    main()
