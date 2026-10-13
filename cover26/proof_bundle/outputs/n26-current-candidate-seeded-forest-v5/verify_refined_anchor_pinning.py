"""Sharper nonlocal N26 pinning: exact arc extrema and per-anchor path errors."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import verify_anchor_pinning as base


def source_gate(basis_folder, stress_folder, local_folder, transport_folder, proposal):
    basis, inventory = base.checked_bundle(basis_folder)
    if (proposal["refinement_basis_acceptance_sha256"] != base.sha(basis_folder / "VERIFIED.json")
            or base.sha(base.__file__) != basis["files"]["verify_anchor_pinning.py"]):
        raise ValueError("refined pinning changed its accepted base arithmetic")
    for path, digest in basis["source_files"].items():
        if base.sha(path) != digest:
            raise ValueError("changed base pinning source")
        inventory.append(base.local_path(path))
    data = base.source_gate(stress_folder, local_folder, transport_folder, proposal)
    mapping = data[3]["native_to_exact_candidate_labels"]
    if any(mapping[str(i)] != i for i in range(16)):
        raise ValueError("refined pinning boundary labels do not match anchor order")
    local = data[4]
    if (not local["exact_rational_polynomial_translation_before_outward_evaluation"]
            or local["basis_source_acceptance_sha256"] != basis["source_acceptance_sha256"]["local"]):
        raise ValueError("refined pinning is not bound to the enlarged same-root local proof")
    return (*data[:5], [*inventory, *data[5]])


def arc_boxes(cells, geometry):
    # The base check supplies root inclusion and short-arc selection. Its
    # deliberately loose midpoint rectangle is replaced by exact extrema.
    base.check_cells(cells, geometry)
    result = [[base.iv.point(1), base.iv.point(0)]]
    quarters = ((F(0), (1, 0)), (F(1, 4), (0, 1)),
                (F(1, 2), (-1, 0)), (F(3, 4), (0, -1)), (F(1), (1, 0)))
    for row in cells:
        lo, hi = map(F, row)
        values = [base.endpoint(lo), base.endpoint(hi)]
        values.extend([[base.iv.point(x), base.iv.point(y)] for turn, (x, y) in quarters if lo <= turn <= hi])
        result.append([(min(p[j][0] for p in values), max(p[j][1] for p in values)) for j in range(2)])
    return result


def derive(original, root, records, path_data, local, proposal):
    if proposal["radius_scope"] != "at-most-the-certified-same-root-Rstar":
        raise ValueError("refined pinning cannot use the larger U threshold")
    support = base.support_gate(proposal, records, path_data)
    geometry, edges, _, t = base.root_geometry(original, root, records)
    if proposal["edges"] != [list(edge) for edge in edges]:
        raise ValueError("refined positive rod support changed")
    scale = int(proposal["rational_scale"])
    if not 10**30 <= scale <= 10**100:
        raise ValueError("invalid refined rational grid")
    p = [[F(int(n), scale) for n in row] for row in proposal["reference_numerators"]]
    weights = [F(int(n), scale) for n in proposal["weight_numerators"]]
    if (len(p) != 62 or any(len(row) != 2 for row in p)
            or len(weights) != len(edges) or min(weights) <= 0 or p[0] != [F(1), F(0)]):
        raise ValueError("invalid refined positive rational network")
    boxes = arc_boxes(proposal["closed_anchor_angle_cells"], geometry)
    epsilons = [base.sqrt_upper(sum(max(abs(a - x), abs(b - x))**2
                                    for (a, b), x in zip(box, point)))
                for box, point in zip(boxes, p[:16])]
    residual = [[F(0), F(0)] for _ in p]
    energy0 = F(0)
    for (u, v), w in zip(edges, weights):
        difference = [a - b for a, b in zip(p[u], p[v])]
        energy0 += w * sum(x * x for x in difference)
        for j, x in enumerate(difference):
            residual[u][j] += w * x
            residual[v][j] -= w * x
    residual_norms = [abs(x) + abs(y) for x, y in residual]
    resistance, parents = base.resistances(len(p), edges, weights)
    anchors = list(range(16))
    for v in range(16, len(p)):
        current, seen = v, set()
        while current >= 16:
            if current in seen or parents[current] is None:
                raise ValueError("refined anchor path is cyclic or unpinned")
            seen.add(current)
            current = parents[current]
        anchors.append(current)
    radial, nonradial, correction = [], [], F(0)
    for v in range(16):
        length2 = sum(x * x for x in p[v])
        if length2 <= 0:
            raise ValueError("zero refined anchor reference")
        k = sum(x * y for x, y in zip(residual[v], p[v])) / length2
        if k <= 0:
            raise ValueError("nonpositive refined radial coefficient")
        radial.append(k)
        nonradial.append(sum(abs(x - k * y) for x, y in zip(residual[v], p[v])))
        correction += k * (length2 - 1)
    K = 2 * sum(residual_norms[v] * base.sqrt_upper(resistance[v]) for v in range(16, len(p)))
    A = (t[1] * sum(weights) - energy0 + correction
         + sum(k * epsilon**2 + 2 * r * epsilon for k, r, epsilon in zip(radial, nonradial, epsilons))
         + 2 * sum(residual_norms[v] * epsilons[anchors[v]] for v in range(16, len(p))))
    Y = K + base.sqrt_upper(max(A, F(0)))
    center_errors = []
    for i in range(26):
        v = 16 + i
        rounding = base.sqrt_upper(sum(max(abs(a - x), abs(b - x))**2
                                        for (a, b), x in zip(geometry[v], p[v])))
        center_errors.append(epsilons[anchors[v]] + base.sqrt_upper(resistance[v]) * Y + rounding)
    allowed = F(local["unrestricted_center_neighbourhood_halfwidth_before_rotation"])
    if max(center_errors) >= allowed:
        raise ValueError("refined nonlocal energy bound does not enter enlarged unrestricted local box")
    return {
        "minimum_positive_support_prefix": support["prefix"],
        "paid_faces_at_support_prefix": len(support["faces"]),
        "support_prefix_terminal": support["terminal"],
        "pinned_anchors": 16, "unrestricted_centers": 26, "unrestricted_internal_witnesses": 20,
        "strictly_positive_weighted_rods": len(edges),
        "closed_anchor_angle_cells": proposal["closed_anchor_angle_cells"],
        "known_exact_root_strictly_inside_all_15_cells": True,
        "exact_arc_endpoint_and_quarter_extrema_enclosures_used": True,
        "individual_anchor_error_bounds": list(map(str, epsilons)),
        "each_path_uses_its_actual_anchor_error_not_global_maximum": True,
        "path_anchor_labels": anchors, "path_parents": parents,
        "all_16_exact_unit_circle_conditions_used": True,
        "unit_circle_corrected_individual_error_energy_slack_A": str(A),
        "internal_residual_coefficient_K": str(K), "sqrt_displacement_energy_upper": str(Y),
        "maximum_center_to_exact_rotated_root_euclidean_error_upper": str(max(center_errors)),
        "accepted_local_box_original_coordinate_halfwidth": str(allowed),
        "strict_entry_margin_to_accepted_local_box": str(allowed - max(center_errors)),
        "no_prior_center_or_internal_witness_neighbourhood_hypothesis": True,
        "conditional_radius_at_least_Rstar_and_only_rotational_equality_proved": True,
        "current_global_frontier_nodes_removed": 0, "covers_angular_complement": False,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--basis", type=Path, required=True)
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--local", type=Path, required=True)
    parser.add_argument("--transport", type=Path, required=True)
    parser.add_argument("--proposal", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    proposal = json.loads(args.proposal.read_text())
    data = source_gate(args.basis, args.stress, args.local, args.transport, proposal)
    result = derive(*data[:5], proposal)
    negatives = []

    def reject(label, changed, gate=False):
        try:
            if gate:
                source_gate(args.basis, args.stress, args.local, args.transport, changed)
            else:
                derive(*data[:5], changed)
        except (ValueError, KeyError, TypeError):
            negatives.append(label)
        else:
            raise AssertionError("bad refined pinning accepted: " + label)

    bad = deepcopy(proposal)
    bad["radius_scope"] = "at-most-U"
    reject("larger-U-threshold", bad)
    bad = deepcopy(proposal)
    bad["minimum_positive_support_prefix"] = [24, 40]
    reject("missing-positive-face-support", bad)
    bad = deepcopy(proposal)
    bad["edges"].pop()
    reject("omitted-positive-rod", bad)
    bad = deepcopy(proposal)
    bad["weight_numerators"][0] = "0"
    reject("nonpositive-rod-weight", bad)
    bad = deepcopy(proposal)
    lo, hi = map(F, bad["closed_anchor_angle_cells"][0])
    bad["closed_anchor_angle_cells"][0] = [str(lo - F(1, 1000)), str(hi + F(1, 1000))]
    reject("root-containing-but-unpinned-large-angle-domain", bad)
    bad = deepcopy(proposal)
    bad["source_acceptance_sha256"]["local"] = "0" * 64
    reject("unbound-enlarged-local-source", bad, gate=True)
    args.output.mkdir(parents=True)
    (args.output / "CERTIFICATE.json").write_bytes(args.proposal.read_bytes())
    modules = ["verify_refined_anchor_pinning.py", "verify_anchor_pinning.py",
               "verify_contact_root.py", "verify_same_root_cover.py",
               "audit_prefix_origin.py", "audit_prefix_partition.py"]
    for name in modules:
        (args.output / name).write_bytes(Path(__file__).with_name(name).read_bytes())
    (args.output / "exact_arcs.py").write_bytes(Path(base.arcs.__file__).read_bytes())
    proof = Path(__file__).with_name("n26-refined-anchor-pinning-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    (args.output / "PROOF.md").write_bytes(proof.read_bytes())
    files = ["CERTIFICATE.json", *modules, "exact_arcs.py", "PROOF.md"]
    report = {
        "schema": "N26-refined-per-anchor-nonlocal-energy-to-centered-local-lower-v1",
        "verified": True, **result,
        "source_acceptance_sha256": proposal["source_acceptance_sha256"],
        "refinement_basis_acceptance_sha256": proposal["refinement_basis_acceptance_sha256"],
        "formal_machine_geometry_proof": False, "full_catalog_complete": False,
        "global_optimality_proved": False, "negative_controls_rejected": negatives,
        "files": {name: base.sha(args.output / name) for name in files},
        "source_files": {str(path): base.sha(path) for path in data[5]},
    }
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    excluded = {"files", "source_files", "individual_anchor_error_bounds", "path_anchor_labels", "path_parents",
                "closed_anchor_angle_cells", "unit_circle_corrected_individual_error_energy_slack_A"}
    print(json.dumps({k: v for k, v in report.items() if k not in excluded}, indent=2), flush=True)


if __name__ == "__main__":
    main()
