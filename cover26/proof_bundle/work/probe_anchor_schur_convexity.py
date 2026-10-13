"""Numerical discovery only: circle-energy Hessians after free-node elimination."""

import argparse
from fractions import Fraction as F
import json
from math import cos, pi
from pathlib import Path

import numpy as np

from n26_sharp_radius_constraints import SCALE
import verify_leaf_pinned_candidate_angles as leaf


def cosine_lower(lo, hi):
    if hi < lo:
        raise ValueError("empty angular difference interval")
    if any(lo <= k + .5 <= hi for k in range(-2, 3)):
        return -1.
    return min(cos(2 * pi * lo), cos(2 * pi * hi))


def hessian_minorant(couplings, matrix, lo=None, hi=None):
    b = len(matrix)
    h = np.zeros((b - 1, b - 1))
    for i in range(b):
        for j in range(i + 1, b):
            low, high = -float(F(matrix[j][i], SCALE)), float(F(matrix[i][j], SCALE))
            if lo is not None:
                low, high = max(low, lo[j] - hi[i]), min(high, hi[j] - lo[i])
            weight = 8 * pi**2 * couplings[i, j] * cosine_lower(low, high)
            v = np.zeros(b - 1)
            if i:
                v[i - 1] -= 1
            if j:
                v[j - 1] += 1
            h += weight * np.outer(v, v)
    return h


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--pinning", type=Path, required=True)
    parser.add_argument("--caps", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    source_report, inventory = leaf.bound(args.source)
    pin_report, files = leaf.bound(args.pinning)
    inventory.extend(files)
    cap_report, files = leaf.bound(args.caps)
    inventory.extend(files)
    if (source_report["source_acceptance_sha256"]["pinning_reference"] != leaf.sha(args.pinning / "VERIFIED.json")
            or source_report["source_acceptance_sha256"]["sharp_caps"] != leaf.sha(args.caps / "VERIFIED.json")):
        raise ValueError("Schur discovery sources differ from accepted same-root graph")
    reference = json.loads((args.pinning / "CERTIFICATE.json").read_text())
    cap = json.loads((args.caps / "CERTIFICATE.json").read_text())
    matrix = json.loads((args.caps / "MATRIX.json").read_text())
    scale = int(reference["rational_scale"])
    weights = [float(F(int(x), scale)) for x in reference["weight_numerators"]]
    laplacian = np.zeros((62, 62))
    for (u, v), w in zip(reference["edges"], weights):
        laplacian[u, u] += w
        laplacian[v, v] += w
        laplacian[u, v] -= w
        laplacian[v, u] -= w
    schur = laplacian[:16, :16] - laplacian[:16, 16:] @ np.linalg.solve(laplacian[16:, 16:], laplacian[16:, :16])
    couplings = np.maximum(-schur, 0.)
    np.fill_diagonal(couplings, 0.)
    global_minimum = float(np.linalg.eigvalsh(hessian_minorant(couplings, matrix))[0])
    tiny = [(0., 0.), *[(float(F(a)), float(F(b))) for a, b in cap["known_candidate_tiny_angle_cells"]]]
    pending = json.loads((args.source / "PENDING-ANGLES.json").read_text())
    results = []
    for row in pending:
        lower = [0., *[float(F(x)) for x in row["sharp_lower"]]]
        upper = [0., *[float(F(x)) for x in row["sharp_upper"]]]
        lo = [min(a, x) for a, (x, y) in zip(lower, tiny)]
        hi = [max(b, y) for b, (x, y) in zip(upper, tiny)]
        minimum = float(np.linalg.eigvalsh(hessian_minorant(couplings, matrix, lo, hi))[0])
        results.append({"index": row["index"], "floating_hessian_lower_eigenvalue": minimum,
                        "root_containing_hull_has_proposed_strict_convexity": minimum > 1e-8})
    proposed = [r["index"] for r in results if r["root_containing_hull_has_proposed_strict_convexity"]]
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-anchor-Schur-energy-convexity-discovery-v1", "verified": False,
        "source_acceptance_sha256": leaf.sha(args.source / "VERIFIED.json"),
        "source_certificate_sha256": leaf.sha(args.source / "CERTIFICATE.json"),
        "pinning_acceptance_sha256": leaf.sha(args.pinning / "VERIFIED.json"),
        "global_domain_floating_Hessian_lower_eigenvalue": global_minimum,
        "proposed_strictly_convex_root_hull_indices": proposed, "results": results,
        "exact_Kron_elimination_trigonometric_LDL_and_energy_entry_proof_pending": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "global_domain_floating_Hessian_lower_eigenvalue": global_minimum,
                      "retained_boxes": len(pending), "proposed_strictly_convex_root_hulls": len(proposed),
                      "minimum_hull_eigenvalue": min(r["floating_hessian_lower_eigenvalue"] for r in results),
                      "maximum_hull_eigenvalue": max(r["floating_hessian_lower_eigenvalue"] for r in results)}), flush=True)


if __name__ == "__main__":
    main()
