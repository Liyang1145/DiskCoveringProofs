"""Explicit positive grounded energy kernels for introduced partial prefixes.

This gate does not accept a full-type certificate under a new label. It
reconstructs exactly the anchors, introduced centers and already present
triangular-face witnesses. Source-prefix ownership and whole-domain transfer
must still be checked by a separate current-frontier acceptance.
"""

from fractions import Fraction as F

from n26_force import rod_graph, spec_gate
import n26_quadratic_energy_minorant as quadratic


SCHEMA = "N26-partial-prefix-positive-ground-energy-kernel-v1"


def graph(spec):
    b, introduced, faces, _ = spec_gate(spec)
    # Independent construction: anchors first, then all introduced centers,
    # then one free witness per already present triangular face.
    edges = []
    for center in range(b):
        edges.append((center, b + center))
    for anchor in range(b):
        edges.append((anchor, b + (anchor + 1) % b))
    for face_index, mask in enumerate(faces):
        members = [center for center in range(introduced) if mask & (1 << center)]
        if len(members) != 3:
            raise ValueError("partial energy witness has a nontriangular present face")
        edges.extend((b + introduced + face_index, b + center) for center in members)
    vertices = b + introduced + len(faces)
    if (vertices, edges) != rod_graph(spec):
        raise ValueError("independent present-prefix rods differ from the necessary rod graph")
    return vertices, edges


def kernel_gate(spec, certificate):
    vertices, edges = graph(spec)
    b, free = spec["B"], vertices - spec["B"]
    if (set(certificate) != {"schema", "spec", "weight_scale", "weight_numerators",
                            "inverse_denominator", "inverse_numerators"}
            or certificate["schema"] != SCHEMA or certificate["spec"] != spec):
        raise ValueError("partial kernel has an unknown schema, different graph or extra fields")
    scale, weights = certificate["weight_scale"], certificate["weight_numerators"]
    if (type(scale) is not int or not 0 < scale <= 10**60
            or not isinstance(weights, list) or len(weights) != len(edges)
            or any(type(w) is not int or not 0 < w or w.bit_length() > 800 for w in weights)):
        raise ValueError("partial positive rod weights or their scale are invalid")
    den = int(certificate["inverse_denominator"])
    inverse = [[int(value) for value in row] for row in certificate["inverse_numerators"]]
    if (den <= 0 or len(inverse) != free or any(len(row) != free for row in inverse)
            or any(inverse[i][j] != inverse[j][i] for i in range(free) for j in range(free))):
        raise ValueError("partial grounded inverse has wrong size, sign or symmetry")
    matrix = [[0] * vertices for _ in range(vertices)]
    adjacency = [set() for _ in range(vertices)]
    for (u, v), weight in zip(edges, weights):
        matrix[u][u] += weight
        matrix[v][v] += weight
        matrix[u][v] -= weight
        matrix[v][u] -= weight
        adjacency[u].add(v)
        adjacency[v].add(u)
    seen, queue = set(range(b)), list(range(b))
    for u in queue:
        for v in adjacency[u]:
            if v not in seen:
                seen.add(v)
                queue.append(v)
    if len(seen) != vertices:
        raise ValueError("a present-prefix free vertex has no path to an anchor")
    # Positive weights plus grounding prove positive definiteness directly
    # by the sum-of-edge-squares identity; no numerical eigenvalue is used.
    for i in range(free):
        for j in range(free):
            product = sum(matrix[b + i][b + k] * inverse[k][j] for k in range(free))
            if product != (den if i == j else 0):
                raise ValueError("exact partial ground inverse identity failed")
    if any(inverse[i][i] <= 0 for i in range(free)):
        raise ValueError("partial grounded inverse has a nonpositive diagonal")
    harmonic = [[-sum(inverse[i][k] * matrix[b + k][j] for k in range(free))
                 for j in range(b)] for i in range(free)]
    if any(min(row) < 0 or sum(row) != den for row in harmonic):
        raise ValueError("partial harmonic extension is not an exact convex combination")
    schur = [[matrix[i][j] * den + sum(matrix[i][b + k] * harmonic[k][j] for k in range(free))
              for j in range(b)] for i in range(b)]
    if (any(sum(row) for row in schur)
            or any(schur[i][j] != schur[j][i] for i in range(b) for j in range(b))
            or any(schur[i][j] > 0 for i in range(b) for j in range(b) if i != j)):
        raise ValueError("partial Schur pair energy identity failed")
    return {"spec": spec, "B": b, "vertices": vertices, "edges": edges,
            "weights": weights, "scale": scale, "matrix": matrix,
            "inverse": inverse, "inverse_denominator": den, "harmonic": harmonic,
            "energy_denominator": scale * den,
            "pairs": [(i, j, -schur[i][j]) for i in range(b)
                      for j in range(i + 1, b) if schur[i][j]]}


def identity_control(kernel):
    """Two-coordinate exact square completion with nonharmonic free points."""
    b, count = kernel["B"], kernel["vertices"] - kernel["B"]
    den, scale = kernel["inverse_denominator"], kernel["scale"]
    anchors = [[F((3 * i + 1) % 7 - 3), F((5 * i + 2) % 11 - 5)] for i in range(b)]
    free = [[F((7 * i + 3) % 13 - 6), F((11 * i + 4) % 17 - 8)] for i in range(count)]
    points = anchors + free
    direct = sum(F(w, scale) * sum((points[u][d] - points[v][d])**2 for d in range(2))
                 for (u, v), w in zip(kernel["edges"], kernel["weights"]))
    boundary = sum(F(w, scale * den) * sum((anchors[i][d] - anchors[j][d])**2 for d in range(2))
                   for i, j, w in kernel["pairs"])
    deviation = [[free[i][d] - sum(F(kernel["harmonic"][i][j], den) * anchors[j][d]
                                  for j in range(b)) for d in range(2)] for i in range(count)]
    residual = sum(F(kernel["matrix"][b + i][b + j], scale) *
                   sum(deviation[i][d] * deviation[j][d] for d in range(2))
                   for i in range(count) for j in range(count))
    if direct != boundary + residual or residual < 0:
        raise ValueError("independent partial two-coordinate square completion failed")
    # A radius-one realization: anchors at rational unit-circle points and
    # every free point at zero. All present rods have length at most one.
    unit_points = [(F(1), F(0)), (F(0), F(1)), (F(-1), F(0)), (F(0), F(-1))]
    feasible = [unit_points[i % 4] for i in range(b)] + [(F(0), F(0))] * count
    feasible_direct = sum(F(w, scale) * sum((feasible[u][d] - feasible[v][d])**2 for d in range(2))
                          for (u, v), w in zip(kernel["edges"], kernel["weights"]))
    feasible_boundary = sum(F(w, scale * den) * sum((feasible[i][d] - feasible[j][d])**2 for d in range(2))
                            for i, j, w in kernel["pairs"])
    if not 0 <= feasible_boundary <= feasible_direct <= F(sum(kernel["weights"]), scale):
        raise ValueError("partial energy method rejected its radius-one rod realization")
    return {"independent_exact_two_coordinate_partial_square_completion": True,
            "positive_grounding_without_numerical_eigenvalues": True,
            "feasible_radius_one_present_rod_control": True,
            "no_unintroduced_centers_or_future_face_witnesses_added": True}


def bound(kernel, matrix, lower, upper, certificate, radius, arcs):
    result = quadratic.bound(kernel, matrix, lower, upper, certificate, radius, arcs)
    return {**result,
            "radius_at_most_Rstar_partial_whole_box_excluded": result[
                "radius_at_most_Rstar_whole_box_excluded"],
            "only_already_present_partial_prefix_rods_used": True}
