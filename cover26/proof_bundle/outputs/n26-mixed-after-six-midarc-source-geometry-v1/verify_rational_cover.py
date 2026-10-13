"""Independent exact Fraction verifier; no numpy, optimizer, or float decisions."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def integer(value):
    if type(value) is not int:
        raise ValueError("integer field required")
    return value


def verify(geometry, certificate):
    if geometry["N"] != 26 or len(geometry["center_numerators"]) != 26:
        raise ValueError("wrong number of centers")
    denominator = integer(geometry["centers_denominator"])
    if denominator <= 0:
        raise ValueError("bad denominator")
    centers = []
    for pair in geometry["center_numerators"]:
        if len(pair) != 2:
            raise ValueError("invalid center")
        centers.append(tuple(F(integer(v), denominator) for v in pair))
    radius = F(geometry["radius"])
    if not 0 < radius < 1:
        raise ValueError("radius outside supported range")
    r2 = radius * radius
    leaves, nodes = {}, set()
    covered = outside = max_depth = 0
    worst_bound = F(0)
    for row in certificate["leaves"]:
        d, i, j = (integer(row[key]) for key in ("depth", "i", "j"))
        if not (0 <= d <= 40 and 0 <= i < 1 << d and 0 <= j < 1 << d):
            raise ValueError("invalid dyadic cell")
        cell = (d, i, j)
        if cell in leaves:
            raise ValueError("duplicate leaf")
        leaves[cell] = row
        nodes.add(cell)
        ancestor = cell
        while ancestor[0]:
            dd, ii, jj = ancestor
            ancestor = dd - 1, ii // 2, jj // 2
            nodes.add(ancestor)
        scale = 1 << d
        xs = (F(-1) + F(2 * i, scale), F(-1) + F(2 * (i + 1), scale))
        ys = (F(-1) + F(2 * j, scale), F(-1) + F(2 * (j + 1), scale))
        if row["kind"] == "covered":
            k = integer(row["center"])
            if not 0 <= k < len(centers):
                raise ValueError("bad center index")
            cx, cy = centers[k]
            # Four explicit exact corner distances, not the builder's scaled
            # farthest-coordinate integer formula.
            corner_bound = max((x - cx) ** 2 + (y - cy) ** 2 for x in xs for y in ys)
            if corner_bound > r2:
                raise ValueError("covered square exceeds radius")
            worst_bound = max(worst_bound, corner_bound)
            covered += 1
        elif row["kind"] == "outside":
            x0 = F(0) if xs[0] <= 0 <= xs[1] else min(xs, key=abs)
            y0 = F(0) if ys[0] <= 0 <= ys[1] else min(ys, key=abs)
            if x0 * x0 + y0 * y0 <= 1:
                raise ValueError("outside leaf meets closed unit disk")
            outside += 1
        else:
            raise ValueError("unpaid leaf")
        max_depth = max(max_depth, d)
    if not leaves or (0, 0, 0) not in nodes:
        raise ValueError("missing root")
    for d, i, j in nodes:
        children = {(d + 1, 2 * i + u, 2 * j + v)
                    for u in (0, 1) for v in (0, 1)}
        if (d, i, j) in leaves:
            if children & nodes:
                raise ValueError("leaf overlaps a descendant")
        elif not children.issubset(nodes):
            raise ValueError("incomplete four-child partition")
    physical_boundary_count = sum(
        (1 - radius) ** 2 <= cx * cx + cy * cy <= (1 + radius) ** 2
        for cx, cy in centers
    )
    return {
        "radius": str(radius), "covered_leaves": covered, "outside_leaves": outside,
        "total_leaves": len(leaves), "total_tree_nodes": len(nodes),
        "maximum_depth": max_depth, "maximum_paid_corner_distance_squared": str(worst_bound),
        "strict_squared_radius_margin": str(r2 - worst_bound),
        "physical_disks_meeting_unit_circle": physical_boundary_count,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--folder", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    gp, cp = args.folder / "geometry.json", args.folder / "cover-certificate.json"
    geometry = json.loads(gp.read_text(encoding="utf-8"))
    certificate = json.loads(cp.read_text(encoding="utf-8"))
    if certificate["geometry_sha256"] != sha(gp):
        raise ValueError("unbound geometry")
    result = verify(geometry, certificate)
    negatives = []

    def reject(label, g, c):
        try:
            verify(g, c)
        except (ValueError, KeyError, TypeError):
            negatives.append(label)
        else:
            raise AssertionError("invalid cover accepted: " + label)

    wrong = deepcopy(certificate)
    wrong["leaves"].pop()
    reject("omitted-leaf", geometry, wrong)
    wrong = deepcopy(certificate)
    wrong["leaves"].append(wrong["leaves"][0])
    reject("duplicate-leaf", geometry, wrong)
    wrong = deepcopy(certificate)
    next(row for row in wrong["leaves"] if row["kind"] == "covered")["kind"] = "outside"
    reject("covered-leaf-falsely-outside", geometry, wrong)
    wrong = deepcopy(certificate)
    next(row for row in wrong["leaves"] if row["kind"] == "covered")["center"] = 26
    reject("invalid-center-index", geometry, wrong)
    wrong_geometry = deepcopy(geometry)
    wrong_geometry["radius"] = "1/10"
    reject("smaller-unproved-radius", wrong_geometry, certificate)
    wrong_geometry = deepcopy(geometry)
    wrong_geometry["center_numerators"] = [[0, 0]] * 26
    reject("substituted-centers", wrong_geometry, certificate)
    wrong = deepcopy(certificate)
    wrong["leaves"].append({"depth": 0, "i": 0, "j": 0,
                            "kind": "outside"})
    reject("overlapping-ancestor", geometry, wrong)
    radius = F(result["radius"])
    alpha = F(3, 2) * (1 - radius * radius)
    if not (alpha > 0 and alpha * alpha > 2):
        raise ValueError("new rational upper not strictly below exact n25 construction")
    report = {
        "schema": "N26-entire-closed-unit-disk-rational-upper-verified-v1",
        "verified": True, "continuous_cover_proved": True,
        "upper_bound_only": True, "global_optimality_proved": False,
        "radius_is_sharp": False,
        "statement": "The 26 specified exact rational centers cover the entire closed unit disk at the stated rational radius.",
        **result, "strictly_below_n25_constructed_radius": True,
        "exact_n25_comparison_gap": str(alpha * alpha - 2),
        "negative_controls_rejected": negatives,
        "files": {str(path): sha(path) for path in (Path(__file__), gp, cp)},
        "proof_scope": "Finite complete dyadic-square partition, exact rational corner containment and strict outside tests; no floating-point acceptance.",
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("files", "negative_controls_rejected")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
