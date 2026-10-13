"""Exact radius-conditional certificates for every selected competitor type.

Standard library only; no optimization or floating-point acceptance.  The
catalogue is reconstructed, the same covering root is replayed, and a second
BFS/Floyd implementation checks the necessary domains and closed partitions.
"""

import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_correlated_arc_force as correlated
import n26_direct_arc_force as direct
import n26_force as force
import n26_sharp_radius_constraints as constraints
import n26_sharp_type_tree as tree
import n26_terminal_canonical as canonical
import verify_anchor_pinning as pin
import verify_contact_root as exact
import verify_positive_stress as stress
import verify_same_root_cover as geometry
import verify_terminal_catalog as catalog
from audit_prefix_partition import linux


SCOPE = "at-most-same-root-Rstar-not-original-U"


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def bound(folder):
    report = read(folder / "VERIFIED.json")
    if not report["verified"] or report["global_optimality_proved"]:
        raise ValueError("unaccepted or overclaimed selected-type dependency")
    inventory = [folder / "VERIFIED.json"]
    for name, digest in {**report["files"], **report.get("additional_files", {})}.items():
        path = folder / name
        if catalog.sha(path) != digest:
            raise ValueError("selected-type dependency bytes changed: " + name)
        inventory.append(path)
    for text, digest in report.get("source_files", {}).items():
        path = catalog.local_path(text)
        if catalog.sha(path) != digest:
            raise ValueError("selected-type historical dependency bytes changed")
        inventory.append(path)
    return report, inventory


def independent_matrix(spec, caps):
    """Rebuild the graph directly, BFS its distances, then Floyd its bounds."""
    n, b, faces = spec["N"], spec["B"], spec["faces"]
    if n != 26 or spec["next"] != n:
        raise ValueError("selected type is not a complete 26-center complex")
    canonical.validate_disk(n, b, faces)
    adjacency = [set() for _ in range(n)]
    for i in range(b):
        j = (i + 1) % b
        adjacency[i].add(j)
        adjacency[j].add(i)
    for face in faces:
        vertices = [i for i in range(n) if face >> i & 1]
        for u in vertices:
            adjacency[u].update(set(vertices) - {u})
    distances = []
    for source in range(n):
        distance, queue = [None] * n, deque([source])
        distance[source] = 0
        while queue:
            u = queue.popleft()
            for v in sorted(adjacency[u]):
                if distance[v] is None:
                    distance[v] = distance[u] + 1
                    queue.append(v)
        if any(value is None for value in distance):
            raise ValueError("selected center graph is disconnected")
        distances.append(distance)
    scale = constraints.SCALE
    edges = {}

    def edge(u, v, value):
        edges[u, v] = min(edges.get((u, v), 2 * scale), value)

    for i in range(b):
        j = (i + 1) % b
        edge(i, j, caps[0] - int(j == 0) * scale)
        edge(j, i, int(j == 0) * scale)
    witnesses = []
    for i in range(b):
        for j in range(i + 1, b):
            h = min(distances[u][v] for u in (i, (i + 1) % b)
                    for v in (j, (j + 1) % b))
            steps = j - i
            if h > 3 or min(steps, b - steps) * caps[0] <= caps[h]:
                continue
            forward = steps * caps[0] < scale - caps[h]
            backward = (b - steps) * caps[0] < scale - caps[h]
            witness = {"anchors": [i, j], "center_path_edges": h,
                       "forward_forced_short": forward,
                       "backward_forced_short": backward}
            witnesses.append(witness)
            if forward and backward:
                return None, {"reason": "both-complementary-arcs-forced-short",
                              "witness": witness}
            if forward:
                edge(i, j, caps[h])
            if backward:
                edge(j, i, caps[h] - scale)
    matrix = [[None] * b for _ in range(b)]
    for i in range(b):
        matrix[i][i] = 0
    for (i, j), value in edges.items():
        matrix[i][j] = value
    for w in range(b):
        for i in range(b):
            for j in range(b):
                if matrix[i][w] is not None and matrix[w][j] is not None:
                    value = matrix[i][w] + matrix[w][j]
                    if matrix[i][j] is None or value < matrix[i][j]:
                        matrix[i][j] = value
    if any(matrix[i][i] < 0 for i in range(b)):
        return None, {"reason": "negative-difference-cycle"}
    if any(value is None for row in matrix for value in row):
        raise ValueError("selected anchor difference graph is disconnected")
    return matrix, {"direct_difference_edges": [[u, v, value]
                    for (u, v), value in sorted(edges.items())],
                    "forced_arc_path_witnesses": witnesses,
                    "center_distances_reconstructed_by_BFS": True,
                    "anchor_closure_reconstructed_by_Floyd": True}


def independently_contract(matrix, lower, upper):
    lo, hi = [F(0), *map(F, lower)], [F(0), *map(F, upper)]
    if len(lo) != len(matrix) or any(a > b for a, b in zip(lo, hi)):
        raise ValueError("malformed closed competitor box")
    result = []
    for target in range(len(matrix)):
        lows = [lo[source] - F(matrix[target][source], constraints.SCALE)
                for source in reversed(range(len(matrix)))]
        highs = [hi[source] + F(matrix[source][target], constraints.SCALE)
                 for source in reversed(range(len(matrix)))]
        result.append((max(lows), min(highs)))
    if any(a > b for a, b in result):
        return None
    if result[0] != (F(0), F(0)):
        raise ValueError("independent contraction changed the rotation gauge")
    return [row[0] for row in result[1:]], [row[1] for row in result[1:]]


def independent_partition(spec, matrix, nodes):
    lower = [F(-matrix[i][0], constraints.SCALE) for i in range(1, spec["B"])]
    upper = [F(matrix[0][i], constraints.SCALE) for i in range(1, spec["B"])]
    queue, seen, leaves = deque([(0, lower, upper)]), set(), []
    while queue:
        index, lower, upper = queue.popleft()
        if type(index) is not int or index in seen or not 0 <= index < len(nodes):
            raise ValueError("independent closed partition repeats or loses a node")
        seen.add(index)
        node = nodes[index]
        box = independently_contract(matrix, lower, upper)
        if box is None:
            if node != {"kind": "EMPTY"}:
                raise ValueError("independent empty domain was not paid as EMPTY")
            leaves.append({"index": index, "kind": "EMPTY"})
            continue
        lower, upper = box
        if node["kind"] == "SPLIT":
            axis, middle, children = node["axis"], F(node["mid"]), node["children"]
            if (type(axis) is not int or not 0 <= axis < len(lower)
                    or not lower[axis] < middle < upper[axis] or len(children) != 2
                    or children[0] == children[1]):
                raise ValueError("independent split does not cover both closed halves")
            left_upper, right_lower = list(upper), list(lower)
            left_upper[axis], right_lower[axis] = middle, middle
            queue.extend(((children[0], list(lower), left_upper),
                          (children[1], right_lower, list(upper))))
        else:
            if node["kind"] not in ("OPEN", "DIRECT_FORCE", "CORRELATED_FORCE"):
                raise ValueError("independent partition has an invalid nonempty leaf")
            leaves.append({"index": index, "kind": node["kind"],
                           "lower": list(map(str, lower)), "upper": list(map(str, upper))})
    if len(seen) != len(nodes):
        raise ValueError("independent partition contains unvisited nodes")
    return sorted(leaves, key=lambda row: row["index"])


def scope_gate(certificate, radius, sources):
    if (certificate["schema"] != "N26-selected-canonical-type-sharp-certificates-v1"
            or certificate["radius_scope"] != SCOPE
            or F(certificate["radius_upper"]) != radius
            or certificate["source_acceptance_sha256"] != sources):
        raise ValueError("selected-type certificate changed its radius, scope or sources")


def coverage_gate(types, table):
    candidates = [i for i, group in enumerate(table["groups"])
                  if any(table["rows"][j]["same_canonical_type_as_known_candidate"]
                         for j in group["member_indices"])]
    if len(candidates) != 1:
        raise ValueError("known feasible type has ambiguous canonical ownership")
    expected = [i for i in range(len(table["groups"])) if i not in candidates]
    if ([row["group_index"] for row in types] != expected
            or any(type(row["group_index"]) is not int for row in types)):
        raise ValueError("a competitor was skipped, duplicated, or replaced by the candidate")
    for row in types:
        group = table["groups"][row["group_index"]]
        if row["spec"] != {"N": 26, "B": group["B"], "next": 26,
                           "faces": group["canonical_faces"]}:
            raise ValueError("competitor geometry was paid on a different canonical graph")
    return candidates[0]


def replay_same_root(folder, accepted):
    original, old_root = read(folder / "ORIGINAL-SYSTEM.json"), read(folder / "ORIGINAL-ROOT-CERTIFICATE.json")
    modified, root = read(folder / "SYSTEM.json"), read(folder / "ROOT-CERTIFICATE.json")
    if (root["system_sha256"] != catalog.sha(folder / "SYSTEM.json")
            or modified["original_system_sha256"] != catalog.sha(folder / "ORIGINAL-SYSTEM.json")
            or root["original_root_certificate_sha256"] != catalog.sha(folder / "ORIGINAL-ROOT-CERTIFICATE.json")):
        raise ValueError("copied same-root sources are not bound")
    polynomials = stress.shape_gate(original, modified)
    old_check = exact.verify(original, old_root, F(1, 10**80))
    root_check = exact.verify(modified, root, F(1, 10**85))
    if old_check != accepted["original_root_check"] or root_check != accepted["modified_root_check"]:
        raise ValueError("same-root isolation did not replay the accepted intervals")
    old_box = stress.interval_root(old_root, F(1, 10**80))[1]
    new_box = stress.interval_root(root, F(1, 10**85))[1]
    if any(not old_box[i][0] < new_box[i][0] < new_box[i][1] < old_box[i][1]
           for i in range(26)):
        raise ValueError("modified covering root escaped original uniqueness box")
    transport = stress.transport_checks(original, root, polynomials)
    if transport != read(folder / "STRESS-LEDGER.json"):
        raise ValueError("same-root contact transport and equilibrium ledger differ")
    cover = geometry.geometry_check(original, root)
    if not cover["same_root_entire_disk_cover_proved"] or not cover["candidate_exact_covering_radius_proved"]:
        raise ValueError("radius endpoint has no same-root continuous covering")
    return original, root, transport, F(root_check["r_strict_interval"][1]), root_check, cover


def candidate_control(original, root, transport, candidate, table, candidate_group, cap, caps, arcs):
    labels = [candidate["native_to_exact_candidate_labels"][str(i)] for i in range(26)]
    native_faces = candidate["states"][-1]["faces"]
    exact_faces = sorted(sum(1 << i for i in face) for face in original["all_faces"])
    if (labels[:16] != list(range(16))
            or canonical.image_faces(native_faces, labels) != exact_faces):
        raise ValueError("known candidate terminal is not the same-root full face complex")
    records = [row for row in transport["full_coordinate_stress_ledger"] if row["orbit"] not in (0, 5, 7)]
    rotated = pin.root_geometry(original, root, records)[0]
    tiny = cap["known_candidate_tiny_angle_cells"]
    pin.check_cells(tiny, rotated)
    source_spec = {"N": 26, "B": 16, "next": 26, "faces": native_faces}
    matrix = independent_matrix(source_spec, caps)[0]
    direct_matrix = constraints.constraint_matrix(source_spec, caps)[0]
    if matrix is None or matrix != direct_matrix:
        raise ValueError("independent sharp domains rejected the known candidate")
    cells = [(F(0), F(0)), *[tuple(map(F, row)) for row in tiny]]
    if any(cells[j][1] - cells[i][0] > F(matrix[i][j], constraints.SCALE)
           for i in range(16) for j in range(16) if i != j):
        raise ValueError("same-root tiny angle control escaped necessary source matrix")
    member = table["groups"][candidate_group]["member_indices"][0]
    mapping = table["rows"][member]["canonical"]["canonical_bijections"][0]
    start, direction = mapping["boundary_start"], mapping["boundary_direction"]
    transformed = [(F(0), F(0))]
    for k in range(1, 16):
        if direction == 1:
            old = (start + k) % 16
            pad = int(old < start)
            transformed.append((cells[old][0] - cells[start][1] + pad,
                                cells[old][1] - cells[start][0] + pad))
        else:
            reference = (start - 1) % 16
            old = (reference - k) % 16
            pad = int(old > reference)
            transformed.append((cells[reference][0] - cells[old][1] + pad,
                                cells[reference][1] - cells[old][0] + pad))
    group = table["groups"][candidate_group]
    canonical_spec = {"N": 26, "B": 16, "next": 26, "faces": group["canonical_faces"]}
    canonical_matrix = independent_matrix(canonical_spec, caps)[0]
    if canonical_matrix is None or canonical_matrix != constraints.constraint_matrix(canonical_spec, caps)[0]:
        raise ValueError("canonical sharp domain rejected the candidate")
    if any(transformed[j][1] - transformed[i][0] > F(canonical_matrix[i][j], constraints.SCALE)
           for i in range(16) for j in range(16) if i != j):
        raise ValueError("boundary rotation/reflection lost the known feasible candidate")
    return {"candidate_group_index": candidate_group,
            "full_34_face_terminal_matches_same_root_center_faces": True,
            "original_exact_root_strictly_inside_all_tiny_cells": True,
            "source_and_canonical_sharp_matrices_both_accept_candidate_tiny_box": True,
            "canonical_boundary_start": start, "canonical_boundary_direction": direction,
            "canonical_closed_tiny_cells": [list(map(str, row)) for row in transformed]}


def input_gate(folder):
    manifest = read(folder / "MANIFEST.json")
    if manifest["schema"] != "N26-selected-sharp-type-input-bindings-v1" or manifest["radius_scope"] != SCOPE:
        raise ValueError("wrong selected-type binding manifest")
    for name, digest in manifest["copied_files"].items():
        if catalog.sha(folder / name) != digest:
            raise ValueError("sealed selected-type input changed: " + name)
    reports, inventory = {}, []
    for key, dirname in (("catalog", "CATALOG-SOURCE"), ("caps", "CAP-SOURCE"), ("stress", "STRESS-SOURCE")):
        report, paths = bound(folder / dirname)
        reports[key] = report
        inventory.extend(paths)
        original = catalog.local_path(manifest["source_folders"][key])
        if (catalog.sha(original / "VERIFIED.json") != manifest["source_acceptance_sha256"][key]
                or catalog.sha(folder / dirname / "VERIFIED.json") != manifest["source_acceptance_sha256"][key]):
            raise ValueError("selected type source acceptance was replaced")
        for name, digest in {**report["files"], **report.get("additional_files", {})}.items():
            if catalog.sha(original / name) != digest:
                raise ValueError("original selected-type source bytes changed")
            inventory.append(original / name)
        inventory.append(original / "VERIFIED.json")
    module_sources = [
        (catalog, "catalog"), (canonical, "catalog"),
        (constraints, "caps"), (direct, "caps"), (force, "caps"), (pin, "caps"),
        (stress, "stress"), (exact, "stress"), (geometry, "stress")]
    for module, source in module_sources:
        name = Path(module.__file__).name
        if catalog.sha(module.__file__) != reports[source]["files"][name]:
            raise ValueError("selected-type checker imported different sealed arithmetic")
    if catalog.sha(correlated.__file__) != manifest["copied_files"]["n26_correlated_arc_force.py"]:
        raise ValueError("unbound correlated-force arithmetic")
    if (catalog.sha(tree.__file__) != manifest["copied_files"]["n26_sharp_type_tree.py"]
            or catalog.sha(pin.arcs.__file__) != reports["caps"]["files"]["exact_arcs.py"]):
        raise ValueError("unbound type-tree or candidate-control arithmetic")
    correlated_source = read(folder / "CORRELATED-SOURCE-ACCEPTANCE.json")
    if (not correlated_source["verified"] or correlated_source["global_optimality_proved"]
            or catalog.sha(correlated.__file__) != correlated_source["files"]["n26_correlated_arc_force.py"]):
        raise ValueError("correlated force does not match its accepted source arithmetic")
    # Native launch records name their actual historical output paths.  The
    # byte-identical copied catalogue is a snapshot, not a forged relocated run.
    cat_folder = catalog.local_path(manifest["source_folders"]["catalog"])
    values = catalog.input_gate(cat_folder)
    table = catalog.reconstruct(cat_folder, *values[1:])
    if (table != read(cat_folder / "CATALOG.json") or table != read(folder / "CATALOG-SOURCE/CATALOG.json")
            or table["selected_terminal_paths"] != 10
            or table["distinct_selected_canonical_types"] != 7 or table["selected_candidate_type_paths"] != 1):
        raise ValueError("all selected native/canonical terminal evidence did not replay")
    accepted_stage, candidate = values[2], values[5]
    stage_folder = values[1]
    inventory.append(stage_folder / "VERIFIED.json")
    inventory.extend(stage_folder / name for name in accepted_stage["files"])
    control = read(cat_folder / "CANDIDATE-ACCEPTANCE.json")
    inventory.extend(catalog.local_path(name) for name in control["files"])
    cap = read(folder / "CAP-SOURCE/CERTIFICATE.json")
    if reports["caps"]["source_stress_acceptance_sha256"] != manifest["source_acceptance_sha256"]["stress"]:
        raise ValueError("sharp caps were certified at a different covering root")
    root_values = replay_same_root(folder / "STRESS-SOURCE", reports["stress"])
    radius = root_values[3]
    arcs, arc_path = force.load_trig(folder)
    inventory.append(arc_path)
    caps, margins = constraints.cap_gate(radius, cap, arcs)
    if list(map(str, margins)) != reports["caps"]["four_strict_outward_sine_margins"]:
        raise ValueError("outward sine margins did not replay")
    certificate = read(folder / "CERTIFICATE.json")
    scope_gate(certificate, radius, manifest["source_acceptance_sha256"])
    candidate_group = coverage_gate(certificate["types"], table)
    positive = candidate_control(*root_values[:3], candidate, table, candidate_group, cap, caps, arcs)
    return manifest, reports, inventory, table, radius, caps, arcs, certificate, positive, root_values


def strict_margin(value, radius):
    margin = F(value) - radius
    if margin <= 0:
        raise ValueError("force payment must be strictly above the certified radius endpoint")
    return margin


def derive(table, certificate, radius, caps, arcs):
    classifications, pending, ledgers, domains = [], [], [], []
    for row in certificate["types"]:
        index, spec = row["group_index"], row["spec"]
        matrix, derivation = constraints.constraint_matrix(spec, caps)
        alternative, independent = independent_matrix(spec, caps)
        if matrix != alternative:
            raise ValueError("independent selected-type matrices disagree")
        if matrix is None:
            if set(row) != {"group_index", "spec", "sharp_domain_empty"} or row["sharp_domain_empty"] is not True:
                raise ValueError("empty necessary root domain has no explicit conditional payment")
            result, boxes, ledger = {"nodes": 0, "counts": {},
                                    "radius_at_most_Rstar_type_excluded": True,
                                    "unresolved_closed_boxes": 0, "minimum_strict_margin": None}, [], []
        else:
            if set(row) != {"group_index", "spec", "nodes"}:
                raise ValueError("nonempty type certificate has unverified fields")
            for node in row["nodes"]:
                if node.get("kind") == "DIRECT_FORCE" and set(node["cert"]) != {"q", "g", "f"}:
                    raise ValueError("direct-force leaf has unverified fields")
            result, boxes, ledger = tree.replay(spec, matrix, radius, row["nodes"], arcs)
            alternative_leaves = independent_partition(spec, alternative, row["nodes"])
            actual_leaves = [{key: leaf[key] for key in ("index", "kind", "lower", "upper") if key in leaf}
                             for leaf in [*boxes, *ledger]]
            if alternative_leaves != sorted(actual_leaves, key=lambda item: item["index"]):
                raise ValueError("independent BFS closed partition differs from exact DFS replay")
            for leaf in ledger:
                if "required_radius_lower" in leaf:
                    strict_margin(leaf["required_radius_lower"], radius)
        group = table["groups"][index]
        members = [{"catalog_member_index": member, "B": table["rows"][member]["B"],
                    "prefix": table["rows"][member]["prefix"],
                    "canonical_bijections": table["rows"][member]["canonical"]["canonical_bijections"]}
                   for member in group["member_indices"]]
        classifications.append({"group_index": index, "spec": spec, "members": members,
                                "radius_scope": SCOPE, **result})
        pending.append({"group_index": index, "spec": spec, "closed_OPEN_boxes": boxes})
        ledgers.append({"group_index": index, "strict_radius_conditional_leaves": ledger})
        domains.append({"group_index": index, "matrix": matrix,
                        "all_pairs_Bellman_Ford_derivation": derivation,
                        "independent_BFS_Floyd_derivation": independent})
        print(json.dumps({"group_index": index, **result}), flush=True)
    return classifications, pending, ledgers, domains


def rejection_controls(table, certificate, radius, caps, arcs, domains):
    negatives = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid selected type accepted: " + label)

    reject("missing-competitor-type", lambda: coverage_gate(certificate["types"][:-1], table))
    reject("duplicated-competitor-type", lambda: coverage_gate(
        [certificate["types"][0], *certificate["types"]], table))
    candidate_group = coverage_gate(certificate["types"], table)
    candidate = table["groups"][candidate_group]
    bad = deepcopy(certificate["types"])
    bad.append({"group_index": candidate_group, "spec": {"N": 26, "B": candidate["B"],
                "next": 26, "faces": candidate["canonical_faces"]}, "nodes": [{"kind": "EMPTY"}]})
    reject("known-feasible-candidate-type-treated-as-competitor", lambda: coverage_gate(bad, table))
    bad = deepcopy(certificate)
    bad["radius_scope"] = "unconditional-original-U-emptiness"
    reject("conditional-exclusion-misreported-as-original-U-empty",
           lambda: scope_gate(bad, radius, certificate["source_acceptance_sha256"]))
    bad = deepcopy(certificate)
    bad["radius_upper"] = "234701/1000000"
    reject("different-radius-threshold", lambda: scope_gate(bad, radius, certificate["source_acceptance_sha256"]))
    bad = deepcopy(certificate["types"])
    bad[0]["spec"]["faces"][0] ^= 1 << 25
    reject("force-paid-on-different-canonical-type", lambda: coverage_gate(bad, table))
    row = next(row for row in certificate["types"] if "nodes" in row)
    matrix = next(domain["matrix"] for domain in domains if domain["group_index"] == row["group_index"])
    spec, nodes = row["spec"], row["nodes"]
    reject("nonempty-entire-type-falsely-declared-empty",
           lambda: tree.replay(spec, matrix, radius, [{"kind": "EMPTY"}], arcs))
    bad = deepcopy(nodes)
    first = next(node for node in bad if node["kind"] == "SPLIT")
    first["children"][1] = first["children"][0]
    reject("one-closed-split-half-lost", lambda: tree.replay(spec, matrix, radius, bad, arcs))
    bad = deepcopy(nodes)
    bad.append({"kind": "OPEN"})
    reject("unvisited-hidden-OPEN-box", lambda: tree.replay(spec, matrix, radius, bad, arcs))
    bad = deepcopy(nodes)
    first = next(node for node in bad if node["kind"] in ("DIRECT_FORCE", "CORRELATED_FORCE"))
    first["cert"]["g"] = [0] * len(first["cert"]["g"])
    first["cert"]["f"] = [0] * len(first["cert"]["f"])
    reject("zero-flow-used-as-strict-type-lower-bound", lambda: tree.replay(spec, matrix, radius, bad, arcs))
    bad = deepcopy(nodes)
    first = next(node for node in bad if node["kind"] == "CORRELATED_FORCE")
    first["cert"]["mu"] = [[0, 1, "-1"]]
    reject("negative-difference-dual", lambda: tree.replay(spec, matrix, radius, bad, arcs))
    reject("nonstrict-radius-equality-payment", lambda: strict_margin(radius, radius))
    member = table["rows"][0]
    mapping = deepcopy(member["canonical"]["canonical_bijections"][0])
    mapping["vertex_to_canonical"][1] = mapping["vertex_to_canonical"][0]
    reject("nonbijective-member-to-paid-canonical-type", lambda: canonical.check_bijection(
        26, member["B"], member["faces"], member["canonical"]["faces"], mapping))
    cap = {"N": 26, "radius_scope": "same-root-Rstar", "radius_upper": str(radius),
           "scale": str(constraints.SCALE), "caps": list(map(str, caps))}
    cap["caps"][0] = "1"
    reject("uncertified-too-small-sharp-cap", lambda: constraints.cap_gate(radius, cap, arcs))
    return negatives


def publish_or_match(path, value):
    if path.exists():
        if read(path) != value:
            raise ValueError("published selected type ledger differs: " + path.name)
    else:
        path.write_text(json.dumps(value, separators=(",", ":")) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    args.input = args.input.resolve()
    if args.report.exists():
        raise FileExistsError(args.report)
    manifest, reports, inventory, table, radius, caps, arcs, certificate, positive, root_values = input_gate(args.input)
    inventory_digests = {linux(path): catalog.sha(path) for path in inventory
                         if not path.resolve().is_relative_to(args.input)}
    classifications, pending, ledgers, domains = derive(table, certificate, radius, caps, arcs)
    controls = correlated.controls(arcs)
    negatives = rejection_controls(table, certificate, radius, caps, arcs, domains)
    for name, value in (("CLASSIFICATION.json", classifications), ("PENDING-TYPES.json", pending),
                        ("LOWER-LEDGER.json", ledgers), ("DOMAINS.json", domains),
                        ("CANDIDATE-POSITIVE-CONTROL.json", positive)):
        publish_or_match(args.input / name, value)
    exclusions = [row["group_index"] for row in classifications if row["radius_at_most_Rstar_type_excluded"]]
    paths = [member for row in classifications if row["radius_at_most_Rstar_type_excluded"] for member in row["members"]]
    names = ["MANIFEST.json", *manifest["copied_files"],
             "CLASSIFICATION.json", "PENDING-TYPES.json", "LOWER-LEDGER.json",
             "DOMAINS.json", "CANDIDATE-POSITIVE-CONTROL.json"]
    report = {
        "schema": "N26-accepted-selected-canonical-type-radius-conditional-certificates-v1",
        "verified": True, "radius_scope": SCOPE, "radius_upper": str(radius),
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "same_root_original_and_modified_isolation_and_contact_transport_replayed": True,
        "same_root_continuous_entire_disk_cover_replayed": True,
        "r_strict_interval": root_values[4]["r_strict_interval"],
        "four_strict_outward_sine_margins": list(map(str, constraints.cap_gate(radius, read(args.input / "CAP-SOURCE/CERTIFICATE.json"), arcs)[1])),
        "all_10_selected_terminal_paths_and_explicit_canonical_bijections_reconstructed": True,
        "all_six_selected_competitor_types_accounted_for": True,
        "independent_BFS_Floyd_and_all_pairs_Bellman_Ford_matrices_agree": True,
        "independent_BFS_closed_partitions_agree_with_exact_DFS": True,
        "both_closed_halves_and_all_shared_boundaries_retained": True,
        "strict_radius_conditional_type_exclusions": exclusions,
        "strict_radius_conditional_terminal_paths_certified": len(paths),
        "unresolved_selected_competitor_types": len(classifications) - len(exclusions),
        "unresolved_selected_competitor_closed_boxes": sum(len(row["closed_OPEN_boxes"]) for row in pending),
        "per_type": [{key: row[key] for key in ("group_index", "nodes", "counts",
                     "radius_at_most_Rstar_type_excluded", "unresolved_closed_boxes", "minimum_strict_margin")}
                     for row in classifications],
        "known_candidate_positive_control": positive,
        "force_positive_controls": controls, "negative_controls_rejected": negatives,
        "original_U_frontier_nodes_removed": 0,
        "Rstar_competitor_frontier_nodes_removed_by_this_bundle": 0,
        "unrestricted_reduction_final_joint_acceptance": False,
        "formal_machine_geometry_proof": False, "full_catalog_complete": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "files": {name: catalog.sha(args.input / name) for name in dict.fromkeys(names)},
        "source_files": inventory_digests,
        "executed_checker_sha256": catalog.sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_selected_type_trees.py"]:
        raise ValueError("executed selected-type checker differs from the sealed checker")
    for name, digest in manifest["copied_files"].items():
        if catalog.sha(args.input / name) != digest:
            raise ValueError("sealed selected-type bytes changed during replay")
    for text, digest in inventory_digests.items():
        if catalog.sha(catalog.local_path(text)) != digest:
            raise ValueError("historical selected-type bytes changed during replay")
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("files", "source_files", "per_type", "known_candidate_positive_control")},
                     indent=2), flush=True)


if __name__ == "__main__":
    main()
