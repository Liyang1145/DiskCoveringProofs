"""Exact nonlocal anchored-rod contraction into the accepted local N26 box.

The hypothesis is a specified partial transport AND a small anchor-angle box,
not prior closeness of any center or internal face witness. Standard library
only. Rational energy/residual estimates, never floating spectral acceptance.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from math import isqrt
from pathlib import Path
import sys

import verify_contact_root as iv
import verify_same_root_cover as geo
from audit_prefix_origin import OriginReference

try:
    import exact_arcs as arcs
except ModuleNotFoundError as exc:
    if exc.name != "exact_arcs":
        raise
    arc_path = Path(__file__).resolve().parent.parent / "outputs/n26-force-stage-v3/exact_arcs.py"
    arc_spec = importlib.util.spec_from_file_location("pinning_exact_arcs", arc_path)
    arcs = importlib.util.module_from_spec(arc_spec)
    arc_spec.loader.exec_module(arcs)


CAPS = (754112, 1555305, 2486507, 3880649)
D = 10**7


def local_path(text):
    text = str(text).replace("\\", "/")
    if sys.platform == "win32" and text.startswith("/mnt/"):
        return Path(text[5].upper() + ":" + text[6:])
    if sys.platform != "win32" and len(text) > 2 and text[1] == ":":
        return Path("/mnt/" + text[0].lower() + text[2:])
    return Path(text)


def sha(path):
    return hashlib.sha256(local_path(path).read_bytes()).hexdigest()


def checked_bundle(folder, absolute=False):
    report_path = folder / "VERIFIED.json"
    report = json.loads(report_path.read_text())
    if not report["verified"] or report["global_optimality_proved"]:
        raise ValueError("unaccepted or overclaimed pinning dependency")
    inventory = [report_path]
    for name, digest in {**report["files"], **report.get("additional_files", {})}.items():
        path = local_path(name) if absolute else folder / name
        if sha(path) != digest:
            raise ValueError("changed pinning dependency: " + str(path))
        inventory.append(path)
    return report, inventory


def source_gate(stress_folder, local_folder, transport_folder, proposal=None):
    stress, inventory = checked_bundle(stress_folder)
    local, paths = checked_bundle(local_folder)
    inventory.extend(paths)
    transport, paths = checked_bundle(transport_folder, absolute=True)
    inventory.extend(paths)
    if (not stress["full_coordinate_equilibrium_proved"]
            or not stress["same_root_equality_proved_by_contact_transport_and_uniqueness"]
            or not local["strict_local_optimality_modulo_rotations_proved"]
            or local["stress_acceptance_sha256"] != sha(stress_folder / "VERIFIED.json")
            or not transport["known_same_root_cover_survives_all_combinatorial_screens"]
            or not transport["native_final_state_independently_matched"]):
        raise ValueError("pinning is not connected to accepted same-root local geometry")
    if proposal is not None and proposal["source_acceptance_sha256"] != {
        "stress": sha(stress_folder / "VERIFIED.json"),
        "local": sha(local_folder / "VERIFIED.json"),
        "transport": sha(transport_folder / "VERIFIED.json"),
    }:
        raise ValueError("pinning proposal changed its accepted sources")
    original = json.loads((stress_folder / "ORIGINAL-SYSTEM.json").read_text())
    root = json.loads((stress_folder / "ROOT-CERTIFICATE.json").read_text())
    rows = json.loads((stress_folder / "STRESS-LEDGER.json").read_text())["full_coordinate_stress_ledger"]
    records = [r for r in rows if r["orbit"] not in (0, 5, 7)]
    path_data = json.loads((transport_folder / "CANDIDATE-PATH.json").read_text())
    if len(records) != 36 or len(original["center_map"]) != 26:
        raise ValueError("wrong positive pinning support")
    return original, root, records, path_data, local, inventory


def norm(p):
    return iv.add(iv.mul(p[0], p[0]), iv.mul(p[1], p[1]))


def anchor(points, t):
    a, b = points
    h, k = [iv.scale(F(1, 2), iv.sub(iv.add(iv.point(1), norm(p)), t)) for p in points]
    determinant = geo.ivcross(a, b)
    return [
        geo.ivdiv(iv.sub(iv.mul(h, b[1]), iv.mul(a[1], k)), determinant),
        geo.ivdiv(iv.sub(iv.mul(a[0], k), iv.mul(h, b[0])), determinant),
    ]


def barycentrics(points, witness):
    a, b, c = points
    u, v, w = [geo.vsub(p, a, iv.sub) for p in (b, c, witness)]
    determinant = geo.ivcross(u, v)
    left = geo.ivdiv(geo.ivcross(w, v), determinant)
    right = geo.ivdiv(geo.ivcross(u, w), determinant)
    return [iv.sub(iv.sub(iv.point(1), left), right), left, right]


def rotate(p, q0):
    return [iv.add(iv.mul(p[0], q0[0]), iv.mul(p[1], q0[1])), geo.ivcross(q0, p)]


def root_geometry(original, root, records):
    rho = F(1, 10**85)
    z = [F(int(n), int(root["Qx"])) for n in root["xnum"]]
    box = [(v - rho, v + rho) for v in z]
    centers = [[iv.point(0) if m["variable"] is None else iv.scale(m["sign"], box[m["variable"]])
                for m in row] for row in original["center_map"]]
    anchors = [anchor([centers[i], centers[(i + 1) % 16]], box[13]) for i in range(16)]
    witnesses, edges, suggested_weights = [], [], []
    for record in records:
        ids = record["vertices"]
        weight = tuple(map(F, record["physical_stress_interval"]))
        if record["kind"] == "face":
            witness = geo.circumcenter(centers, ids)
            coefficients = barycentrics([centers[i] for i in ids], witness)
            u = 42 + len(witnesses)
            witnesses.append(witness)
        elif record["kind"] == "boundary" and ids[1] == (ids[0] + 1) % 16:
            u = ids[0]
            witness = anchors[u]
            ta, tb = [geo.ivcross(witness, centers[i]) for i in ids]
            left = geo.ivdiv(iv.scale(-1, tb), iv.sub(ta, tb))
            coefficients = [left, iv.sub(iv.point(1), left)]
        else:
            raise ValueError("unrecognized pinning contact")
        if any(c[0] <= 0 for c in coefficients):
            raise ValueError("nonpositive rod stress in the suggested support")
        for i, coefficient in zip(ids, coefficients):
            edges.append((u, 16 + i))
            suggested_weights.append(iv.mul(weight, coefficient))
    q0 = anchors[0]
    rotated = [rotate(p, q0) for p in [*anchors, *centers, *witnesses]]
    # The accepted same-root cover proves |q0|=1; rotate(q0,q0)=(1,0).
    rotated[0] = [iv.point(1), iv.point(0)]
    if len(rotated) != 62 or len(edges) != 92:
        raise ValueError("unexpected positive anchored network")
    return rotated, edges, suggested_weights, box[13]


def endpoint(turn):
    co, si = arcs.sincos_turn(F(turn))
    return [(F(co[0], arcs.SCALE), F(co[1], arcs.SCALE)),
            (F(si[0], arcs.SCALE), F(si[1], arcs.SCALE))]


def check_cells(cells, geometry):
    if len(cells) != 15 or not 3 * arcs.SCALE < arcs.PI[0] <= arcs.PI[1] < 4 * arcs.SCALE:
        raise ValueError("wrong anchor cells or missing rational pi bound")
    result = [[iv.point(1), iv.point(0)]]
    for i, cell in enumerate(cells, 1):
        lo, hi = map(F, cell)
        if not 0 < lo < hi < 1 or hi - lo >= F(1, 4):
            raise ValueError("invalid small closed anchor-angle cell")
        if (geo.ivcross(endpoint(lo), geometry[i])[0] <= 0
                or geo.ivcross(geometry[i], endpoint(hi))[0] <= 0):
            raise ValueError("known exact root not strictly contained in anchor cell")
        # Along a unit-circle parametrization each coordinate has speed <=2pi<8.
        middle = endpoint((lo + hi) / 2)
        pad = 4 * (hi - lo)
        result.append([(a - pad, b + pad) for a, b in middle])
    return result


def sqrt_upper(value, scale=10**70):
    value = F(value)
    if value < 0:
        raise ValueError("negative pinning square-root argument")
    k = isqrt(value.numerator * scale**2 // value.denominator)
    if F(k * k, scale**2) < value:
        k += 1
    return F(k, scale)


def resistances(vertices, edges, weights):
    adjacency = [[] for _ in range(vertices)]
    for (u, v), w in zip(edges, weights):
        adjacency[u].append((v, 1 / w))
        adjacency[v].append((u, 1 / w))
    # Exact multi-source shortest paths supply explicit anchor paths. Effective
    # resistances are NOT assumed equal to these deliberately loose path bounds.
    values = [F(0) if i < 16 else None for i in range(vertices)]
    parents = [None] * vertices
    todo = set(range(vertices))
    while todo:
        reachable = [i for i in todo if values[i] is not None]
        if not reachable:
            raise ValueError("positive rod support does not pin every center/witness")
        u = min(reachable, key=lambda i: (values[i], i))
        todo.remove(u)
        for v, cost in adjacency[u]:
            if v not in todo:
                continue
            proposed = values[u] + cost
            if values[v] is None or proposed < values[v]:
                values[v], parents[v] = proposed, u
    return values, parents


def support_gate(proposal, records, path_data):
    mapping = {int(k): v for k, v in path_data["native_to_exact_candidate_labels"].items()}
    if sorted(mapping) != list(range(26)) or sorted(mapping.values()) != list(range(26)):
        raise ValueError("transport label map is not bijective")
    required = {frozenset(r["vertices"]) for r in records if r["kind"] == "face"}
    eligible = []
    reference = OriginReference(26, 16, "dfs", caps=CAPS, scale=D)
    for row in path_data["states"]:
        if row["next"] != 26:
            continue
        faces = {frozenset(mapping[i] for i in range(26) if mask >> i & 1) for mask in row["faces"]}
        if required <= faces:
            eligible.append(row)
    if not eligible:
        raise ValueError("known candidate transport lacks necessary positive faces")
    chosen = min(eligible, key=lambda row: len(row["prefix"]))
    if (proposal["B"] != 16 or proposal["N"] != 26
            or proposal["minimum_positive_support_prefix"] != chosen["prefix"]):
        raise ValueError("pinning applied before its full positive face support is present")
    state = reference.resolve(tuple(chosen["prefix"]))
    expected = reference.entry(tuple(chosen["prefix"]), state, reference.children(state))
    if chosen != expected or state.next_vertex != 26:
        raise ValueError("pinning prefix disagrees with independent recurrence")
    return chosen


def derive(original, root, records, path_data, local, proposal):
    if proposal["radius_scope"] != "at-most-the-certified-same-root-Rstar":
        raise ValueError("pinning cannot substitute the wider enumeration threshold U")
    support = support_gate(proposal, records, path_data)
    geometry, edges, _, t = root_geometry(original, root, records)
    if proposal["edges"] != [list(edge) for edge in edges]:
        raise ValueError("pinning rod support changed or omitted")
    scale = int(proposal["rational_scale"])
    if not 10**30 <= scale <= 10**100:
        raise ValueError("invalid rational pinning grid")
    p = [[F(int(x), scale) for x in row] for row in proposal["reference_numerators"]]
    weights = [F(int(n), scale) for n in proposal["weight_numerators"]]
    if (len(p) != 62 or any(len(row) != 2 for row in p)
            or len(weights) != len(edges) or min(weights) <= 0
            or p[0] != [F(1), F(0)]):
        raise ValueError("invalid positive rational pinning network")
    anchor_box = check_cells(proposal["closed_anchor_angle_cells"], geometry)
    epsilon = max(sqrt_upper(sum(max(abs(a - x), abs(b - x))**2
                                  for (a, b), x in zip(box, point)))
                  for box, point in zip(anchor_box, p[:16]))
    residual = [[F(0), F(0)] for _ in p]
    energy0 = F(0)
    for (u, v), weight in zip(edges, weights):
        difference = [a - b for a, b in zip(p[u], p[v])]
        energy0 += weight * sum(x * x for x in difference)
        for j, x in enumerate(difference):
            residual[u][j] += weight * x
            residual[v][j] -= weight * x
    residual_norms = [abs(x) + abs(y) for x, y in residual]
    resistance, parents = resistances(len(p), edges, weights)
    K = 2 * sum(residual_norms[v] * sqrt_upper(resistance[v]) for v in range(16, len(p)))
    A = t[1] * sum(weights) - energy0 + 2 * epsilon * sum(residual_norms)
    Y = K + sqrt_upper(max(A, F(0)))
    distances = [epsilon + sqrt_upper(resistance[v]) * Y for v in range(16, len(p))]
    center_errors = []
    for i in range(26):
        v = 16 + i
        rounding = sqrt_upper(sum(max(abs(a - x), abs(b - x))**2
                                  for (a, b), x in zip(geometry[v], p[v])))
        center_errors.append(distances[i] + rounding)
    allowed = F(local["unrestricted_center_neighbourhood_halfwidth_before_rotation"])
    if max(center_errors) >= allowed:
        raise ValueError("anchored energy bound does not enter accepted unrestricted local box")
    return {
        "specified_partial_transport_positive_support_independently_reconstructed": True,
        "minimum_positive_support_prefix": support["prefix"],
        "paid_faces_at_support_prefix": len(support["faces"]),
        "all_26_centers_already_introduced": True,
        "support_prefix_terminal": support["terminal"],
        "pinned_anchors": 16, "unrestricted_centers": 26, "unrestricted_internal_witnesses": 20,
        "strictly_positive_weighted_rods": len(edges),
        "closed_anchor_angle_cells": proposal["closed_anchor_angle_cells"],
        "known_exact_root_in_strict_interior_of_all_15_angle_cells": True,
        "maximum_angle_cell_width_turns": str(max(F(b) - F(a) for a, b in proposal["closed_anchor_angle_cells"])),
        "anchor_reference_euclidean_error_upper": str(epsilon),
        "radius_squared_weight_sum_minus_reference_energy_plus_anchor_residual_bound": str(A),
        "internal_residual_coefficient_K": str(K),
        "sqrt_displacement_energy_upper": str(Y),
        "maximum_anchor_path_resistance_upper": str(max(resistance[16:])),
        "maximum_center_to_exact_rotated_root_euclidean_error_upper": str(max(center_errors)),
        "accepted_local_box_original_coordinate_halfwidth": str(allowed),
        "strict_entry_margin_to_accepted_local_box": str(allowed - max(center_errors)),
        "path_parents": parents,
        "no_prior_center_or_internal_witness_neighbourhood_hypothesis": True,
        "conditional_radius_at_least_Rstar_and_only_rotational_equality_proved": True,
        "covers_angular_complement": False,
        "current_global_frontier_nodes_removed": 0,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--local", type=Path, required=True)
    parser.add_argument("--transport", type=Path, required=True)
    parser.add_argument("--proposal", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    proposal = json.loads(args.proposal.read_text())
    original, root, records, path_data, local, inventory = source_gate(
        args.stress, args.local, args.transport, proposal)
    result = derive(original, root, records, path_data, local, proposal)
    negatives = []

    def reject(label, candidate, gate=False):
        try:
            if gate:
                source_gate(args.stress, args.local, args.transport, candidate)
            else:
                derive(original, root, records, path_data, local, candidate)
        except (ValueError, KeyError, TypeError):
            negatives.append(label)
        else:
            raise AssertionError("bad pinning accepted: " + label)

    bad = deepcopy(proposal)
    bad["radius_scope"] = "at-most-U"
    reject("wider-U-is-not-sharp-Rstar", bad)
    bad = deepcopy(proposal)
    bad["minimum_positive_support_prefix"] = [24, 40]
    reject("broad-candidate-owner-with-missing-positive-faces", bad)
    bad = deepcopy(proposal)
    bad["edges"].pop()
    reject("omitted-required-rod", bad)
    bad = deepcopy(proposal)
    bad["weight_numerators"][0] = "0"
    reject("nonpositive-rod-weight", bad)
    bad = deepcopy(proposal)
    bad["closed_anchor_angle_cells"][0] = ["0", "1/4"]
    reject("unisolated-large-anchor-cell", bad)
    bad = deepcopy(proposal)
    lo, hi = map(F, bad["closed_anchor_angle_cells"][0])
    bad["closed_anchor_angle_cells"][0] = [str(lo - F(1, 10**12)), str(hi + F(1, 10**12))]
    reject("root-containing-but-insufficiently-contracted-anchor-cell", bad)
    bad = deepcopy(proposal)
    bad["source_acceptance_sha256"]["local"] = "0" * 64
    reject("unbound-local-lower-source", bad, gate=True)
    args.output.mkdir(parents=True)
    (args.output / "CERTIFICATE.json").write_bytes(args.proposal.read_bytes())
    (args.output / "verify_anchor_pinning.py").write_bytes(Path(__file__).read_bytes())
    proof = Path(__file__).with_name("n26-anchor-pinning-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    (args.output / "PROOF.md").write_bytes(proof.read_bytes())
    modules = ["verify_contact_root.py", "verify_same_root_cover.py", "exact_arcs.py",
               "audit_prefix_origin.py", "audit_prefix_partition.py"]
    for name in modules:
        source = Path(arcs.__file__) if name == "exact_arcs.py" else Path(__file__).with_name(name)
        (args.output / name).write_bytes(source.read_bytes())
    files = ["CERTIFICATE.json", "verify_anchor_pinning.py", "PROOF.md", *modules]
    report = {
        "schema": "N26-nonlocal-anchor-energy-to-unrestricted-local-lower-v1",
        "verified": True, **result, "global_optimality_proved": False,
        "full_catalog_complete": False, "formal_machine_geometry_proof": False,
        "negative_controls_rejected": negatives,
        "source_acceptance_sha256": proposal["source_acceptance_sha256"],
        "files": {name: sha(args.output / name) for name in files},
        "source_files": {str(path): sha(path) for path in inventory},
    }
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("files", "source_files", "closed_anchor_angle_cells", "path_parents")},
                     indent=2), flush=True)


if __name__ == "__main__":
    main()
