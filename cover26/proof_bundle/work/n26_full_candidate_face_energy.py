"""Distinct all34face/134rod/60free positive kernels and exact energy bounds.

Pure arithmetic: no typed resource, diagnostic producer or history cache is
imported. Geometry callers still need the ENTIRE actual latest source gate.
No old92rod/46free kernel flag is forged or old model changed.
"""

from fractions import Fraction as F
from math import isqrt

from audit_prefix_origin import OriginReference
from n26_force import CAPS, D
import n26_dirichlet_energy as direct
import n26_partial_prefix_quadratic_kernel as native_graph
import n26_signed_hull_energy_minorant as hull


SCHEMA = "N26-distinct-all34face-134rod-60free-positive-ground-kernel-v1"
MODE = "NEW-ALL34FACE-POSITIVE-SUPPORT"


def model_gate(system, old_reference, path):
    if (system["N"] != 26 or system["B"] != 16
            or old_reference["N"] != 26 or old_reference["B"] != 16
            or len(old_reference["edges"]) != 92 or len(old_reference["weight_numerators"]) != 92):
        raise ValueError("full-face arithmetic changed the original source/frame")
    labels = {int(key): value for key, value in path["native_to_exact_candidate_labels"].items()}
    if (sorted(labels) != list(range(26)) or sorted(labels.values()) != list(range(26))
            or any(type(value) is not int for value in labels.values())
            or any(labels[index] != index for index in range(16))):
        raise ValueError("full-face arithmetic changed the actual center/anchor source bijection")
    final = path["states"][-1]
    if (final["prefix"] != path["prefix"] or final["terminal"] is not True
            or final["next"] != 26 or final["pending"] or len(final["faces"]) != 34):
        raise ValueError("full-face arithmetic requires the actual complete34face candidate")
    reference = OriginReference(26, 16, "dfs", caps=CAPS, scale=D)
    state = reference.resolve(tuple(final["prefix"]))
    if reference.entry(tuple(final["prefix"]), state, reference.children(state)) != final:
        raise ValueError("full-face arithmetic complete source terminal did not reconstruct")
    faces = [tuple(face) for face in system["all_faces"]]
    if (len(faces) != 34 or len(set(faces)) != 34
            or any(len(face) != 3 or list(face) != sorted(set(face)) for face in faces)
            or any(type(index) is not int or not 0 <= index < 26 for face in faces for index in face)
            or set(faces) != {
                tuple(sorted(labels[center] for center in range(26) if mask >> center & 1))
                for mask in final["faces"]}):
        raise ValueError("full-face arithmetic has a different, missing or repeated source face")
    witnesses = {index: set() for index in range(42, 62)}
    boundary = {index: set() for index in range(16)}
    edges = old_reference["edges"]
    if len({tuple(sorted(edge)) for edge in edges}) != 92:
        raise ValueError("full-face arithmetic old92rod source repeats an edge")
    for edge in edges:
        if (not isinstance(edge, list) or len(edge) != 2
                or any(type(index) is not int or not 0 <= index < 62 for index in edge)):
            raise ValueError("full-face arithmetic old rod endpoint is invalid")
        u, v = edge
        if 42 <= u < 62 and 16 <= v < 42:
            witnesses[u].add(v-16)
        elif 0 <= u < 16 and 16 <= v < 32:
            boundary[u].add(v-16)
        else:
            raise ValueError("full-face arithmetic old rod is outside its actual face/boundary source")
    selected = [tuple(sorted(witnesses[index])) for index in range(42, 62)]
    if (any(len(face) != 3 for face in selected) or len(set(selected)) != 20
            or not set(selected) <= set(faces)
            or any(boundary[index] != {index, (index+1) % 16} for index in range(16))):
        raise ValueError("full-face arithmetic original20face/32boundary support changed")
    missing = [face for face in faces if face not in set(selected)]
    expanded = [list(edge) for edge in edges]
    face_vertices = {face: vertex for vertex, face in zip(range(42, 62), selected)}
    for vertex, face in enumerate(missing, 62):
        face_vertices[face] = vertex
        expanded.extend([[vertex, 16+center] for center in face])
    spec = {"N": 26, "B": 16, "next": 26, "faces": final["faces"]}
    vertices, actual = native_graph.graph(spec)
    permutation = {index: index for index in range(16)}
    permutation.update({16+index: 16+value for index, value in labels.items()})
    for vertex, mask in enumerate(final["faces"], 42):
        face = tuple(sorted(labels[center] for center in range(26) if mask >> center & 1))
        permutation[vertex] = face_vertices[face]
    if (vertices != 76 or len(missing) != 14 or len(expanded) != 134
            or sorted(permutation.values()) != list(range(76))
            or {tuple(sorted(edge)) for edge in expanded} != {
                tuple(sorted((permutation[u], permutation[v]))) for u, v in actual}):
        raise ValueError("full-face arithmetic134rod model differs from the independent actual native graph")
    return {
        "edges": expanded, "vertices": 76, "anchors": 16, "free": 60,
        "actual_all34face_source_checked": True,
        "all_original92rods_identical_prefix_retained": True,
        "native_to_extended_vertex_bijection": permutation,
    }


def kernel_gate(model, certificate):
    if (set(certificate) != {"schema", "mode", "weight_scale", "weight_numerators",
                            "inverse_denominator", "inverse_numerators"}
            or certificate["schema"] != SCHEMA or certificate["mode"] != MODE
            or model["vertices"] != 76 or model["anchors"] != 16 or model["free"] != 60
            or model["actual_all34face_source_checked"] is not True or len(model["edges"]) != 134):
        raise ValueError("full-face positive kernel has a wrong explicit source mode or dimension")
    scale, weights = certificate["weight_scale"], certificate["weight_numerators"]
    if (type(scale) is not int or not 0 < scale <= 10**60
            or not isinstance(weights, list) or len(weights) != 134
            or any(type(weight) is not int or not 0 < weight or weight.bit_length() > 800 for weight in weights)):
        raise ValueError("full-face positive kernel has invalid weights/NEW scale")
    matrix = direct.laplacian(model["edges"], weights, vertices=76)
    denominator = int(certificate["inverse_denominator"])
    inverse = [[int(value) for value in row] for row in certificate["inverse_numerators"]]
    if (denominator <= 0 or len(inverse) != 60 or any(len(row) != 60 for row in inverse)
            or any(inverse[i][j] != inverse[j][i] for i in range(60) for j in range(60))):
        raise ValueError("full-face NEW60ground inverse has a wrong size, sign or symmetry")
    for i in range(60):
        for j in range(60):
            if sum(matrix[16+i][16+k]*inverse[k][j] for k in range(60)) != (
                    denominator if i == j else 0):
                raise ValueError("full-face NEW exact60ground inverse identity failed")
    if any(inverse[index][index] <= 0 for index in range(60)):
        raise ValueError("full-face grounded inverse has a nonpositive resistance")
    harmonic = [[-sum(inverse[i][k]*matrix[16+k][j] for k in range(60))
                 for j in range(16)] for i in range(60)]
    if any(min(row) < 0 or sum(row) != denominator for row in harmonic):
        raise ValueError("full-face harmonic extension is not an exact convex combination")
    schur = [[matrix[i][j]*denominator+sum(matrix[i][16+k]*harmonic[k][j] for k in range(60))
              for j in range(16)] for i in range(16)]
    if (any(sum(row) for row in schur)
            or any(schur[i][j] != schur[j][i] for i in range(16) for j in range(16))
            or any(schur[i][j] > 0 for i in range(16) for j in range(16) if i != j)):
        raise ValueError("full-face Schur energy/positive pair identity failed")
    pairs = [(i, j, -schur[i][j]) for i in range(16) for j in range(i+1, 16) if schur[i][j]]
    return {
        "B": 16, "vertices": 76, "edges": model["edges"], "weights": weights, "scale": scale,
        "matrix": matrix, "inverse": inverse, "inverse_denominator": denominator,
        "harmonic": harmonic, "energy_denominator": scale*denominator,
        "pairs": pairs, "pair_weights": pairs,
        "distinct_full134rod_60free_positive_candidate_kernel": True,
    }


def combined_minorant(kernel, matrix, reference, lower, upper, arcs, parts):
    if (type(parts) is not int or not 1 <= parts <= 256
            or kernel.get("distinct_full134rod_60free_positive_candidate_kernel") is not True
            or kernel.get("original_candidate_92_rod_46_free_vertex_kernel") is not None
            or kernel["vertices"] != 76 or len(kernel["weights"]) != 134):
        raise ValueError("full-face integrated bound changed its NEW model or exact strip count")
    ref, lo, hi, _, _ = hull.hull_gate(reference, lower, upper, matrix)
    combined, total = [[F(0)]*15 for _ in range(15)], F(0)
    for index in range(parts):
        left, right = F(index, parts), F(index+1, parts)
        weight = F(2*parts-2*index-1, parts**2)
        a, b = [], []
        for r, x, y in zip(ref[1:], lo[1:], hi[1:]):
            endpoints = [r+t*(value-r) for t in (left, right) for value in (x, y)]
            a.append(min(endpoints))
            b.append(max(endpoints))
        minorant = hull.quadratic.hessian_minorant(kernel, matrix, a, b, arcs)
        for i in range(15):
            for j in range(15):
                combined[i][j] += weight*minorant[i][j]
        total += weight
    if total != 1 or any(combined[i][j] != combined[j][i] for i in range(15) for j in range(15)):
        raise AssertionError("full-face exact normalized Taylor strips lost coverage or symmetry")
    return combined


def bound(kernel, matrix, lower, upper, certificate, radius, arcs):
    if set(certificate) != {"reference_turns", "parts", "signed_eta", "difference_dual"}:
        raise ValueError("full-face energy certificate has unknown or missing distinct fields")
    combined = combined_minorant(
        kernel, matrix, certificate["reference_turns"], lower, upper, arcs, certificate["parts"])
    ref, lo, hi, _, _ = hull.hull_gate(certificate["reference_turns"], lower, upper, matrix)
    eta = list(map(F, certificate["signed_eta"]))
    if len(eta) != 15 or any(abs(value) > 10**60 for value in eta):
        raise ValueError("full-face bound has an invalid signed diagonal")
    allowance = F(15, hull.quadratic.ROUND_GRID)
    pivots = hull.quadratic.positive_ldl([
        [value+(eta[i]-allowance if i == j else 0) for j, value in enumerate(row)]
        for i, row in enumerate(combined)])
    point, gradient = hull.outward_point_values(kernel, ref, arcs)
    support, controls = hull.support(ref, lo, hi, matrix, gradient, eta, certificate["difference_dual"])
    lower_energy = point+support
    weight_sum = F(sum(kernel["weights"]), kernel["scale"])
    upper_energy = F(radius)**2*weight_sum
    normalized, grid = max(F(0), lower_energy)/weight_sum, 10**100
    radius_lower = F(isqrt(normalized.numerator*grid**2//normalized.denominator), grid)
    if not radius_lower**2 <= normalized < (radius_lower+F(1, grid))**2:
        raise AssertionError("full-face energy outward radius conversion failed")
    return {
        "boundary_full134rod_energy_lower": str(lower_energy),
        "NEW_full134rod_energy_upper_at_same_root": str(upper_energy),
        "strict_energy_margin": str(lower_energy-upper_energy),
        "strict_radius_margin": str(radius_lower-F(radius)),
        "arithmetic_strict_target_test_passed": lower_energy > upper_energy and radius_lower > F(radius),
        "distinct_full134rod_76vertex_60free_kernel_NOT_original92rod": True,
        "all_closed_Taylor_strips_and_exact_normalized_weights_sum1_checked": certificate["parts"],
        "weighted_symmetric_rounding_operator_error_charged": str(allowance),
        "exact_positive_LDL_minimum_pivot": str(min(pivots)), **controls,
        "verified": False, "new_geometric_payments": 0,
        "complete_latest_source_model_history_geometry_admission_NOT_performed": True,
    }
