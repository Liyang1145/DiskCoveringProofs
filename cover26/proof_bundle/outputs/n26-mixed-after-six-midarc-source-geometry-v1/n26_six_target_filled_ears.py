"""Exact six-target identities, filled-patch recognition and original counts."""

from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations

from audit_prefix_origin import validate_disk


U = F(234701, 1000000)


def family_gate(constants):
    if (
        constants["N"] != 26 or F(constants["radius_upper"]) != U
        or constants["minimum_interior_cells"] != 9
        or constants["minimum_boundary_cells"] != 14
        or constants["maximum_boundary_cells"] != 17
        or constants["external_n8_theorem_assumed"] is not True
        or constants["n8_reproved_here"] is not False
        or constants["families"] != [[14, 12], [15, 11], [16, 10], [17, 9]]
    ):
        raise ValueError("six-target source lacks the explicit original-owner external family premise")


def target_gate(u=U, points=None):
    r, h = 1-2*u, F(4, 5)-u
    # A coordinate (x,t) means actual point (x,sqrt(3)*t).
    expected = [(F(0), F(0)), (r/2, r/2), (r/2, -r/2),
                (-r/2, r/2), (-r/2, -r/2), (-r, F(0))]
    points = expected if points is None else points
    if len(points) != 6 or len(set(points)) != 6 or not 0 < u < F(1, 4):
        raise ValueError("six exact distinct targets or strict cover-radius scope missing")
    squared = [(left[0]-right[0])**2+3*(left[1]-right[1])**2
               for left, right in combinations(points, 2)]
    norms = [x*x+3*y*y for x, y in points]
    if (
        any(value > r*r for value in norms)
        or min(squared) <= 4*u*u
        or h-max(x for x, y in points) <= u
    ):
        raise ValueError("targets are outside the core, insufficiently separated, or accessible from the ear")
    return {
        "exact_six_targets_x_and_sqrt3_y_coefficients": [[str(x), str(y)] for x, y in points],
        "exact_core_radius": str(r),
        "exact_minimum_squared_pair_distance": str(min(squared)),
        "exact_squared_pair_margin_above_four_U_squared": str(min(squared)-4*u*u),
        "exact_ear_to_all_targets_horizontal_distance_lower": str(h-max(x for x, y in points)),
        "exact_horizontal_margin_above_U": str(h-max(x for x, y in points)-u),
        "six_DISTINCT_ORIGINAL_outside_nonowner_disks_required": 6,
        "finite_identities_do_NOT_replace_the_written_continuous_cover_and_embedding_proof": True,
    }


def independent_disk_gate(b, masks, owners):
    """Links, edge incidence and face connectivity; does not use validate_disk."""
    triangles = [tuple(v for v in range(26) if mask & (1 << v)) for mask in masks]
    if not triangles or any(len(face) != 3 for face in triangles) or len(set(triangles)) != len(triangles):
        return False
    vertices = {v for face in triangles for v in face}
    if vertices & set(range(b)) != set(owners):
        return False
    sides, at_vertex = defaultdict(list), defaultdict(list)
    for index, face in enumerate(triangles):
        for edge in combinations(face, 2):
            sides[edge].append(index)
        for v in face:
            at_vertex[v].append(face)
    boundary = set(combinations(sorted(owners), 2))
    if (
        any(len(incident) not in (1, 2) for incident in sides.values())
        or {edge for edge, incident in sides.items() if len(incident) == 1} != boundary
        or len(vertices)-len(sides)+len(triangles) != 1
    ):
        return False
    dual = [set() for _ in triangles]
    for incident in sides.values():
        if len(incident) == 2:
            left, right = incident
            dual[left].add(right)
            dual[right].add(left)
    reached, queue = {0}, [0]
    for index in queue:
        for neighbor in dual[index]-reached:
            reached.add(neighbor)
            queue.append(neighbor)
    if len(reached) != len(triangles):
        return False
    for vertex in vertices:
        links = defaultdict(set)
        for face in at_vertex[vertex]:
            left, right = [v for v in face if v != vertex]
            links[left].add(right)
            links[right].add(left)
        expected_ends = set(owners)-{vertex} if vertex in owners else set()
        if (
            {v for v, neighbors in links.items() if len(neighbors) == 1} != expected_ends
            or any(len(neighbors) not in (1, 2) for neighbors in links.values())
        ):
            return False
        start = next(iter(links))
        reached, queue = {start}, [start]
        for v in queue:
            for w in links[v]-reached:
                reached.add(w)
                queue.append(w)
        if reached != set(links):
            return False
    return True


def patch_certificate(row, owners, indices):
    b = row["B"]
    masks = [row["faces"][index] for index in sorted(indices)]
    vertices = {v for mask in masks for v in range(row["next"]) if mask & (1 << v)}
    interior = sorted(vertices-set(range(b)))
    if vertices & set(range(b)) != set(owners) or 26-b-len(interior) >= 6:
        return None
    remap = {v: offset for offset, v in enumerate(owners+interior)}
    compacted = [sum(1 << remap[v] for v in vertices if mask & (1 << v)) for mask in masks]
    try:
        edges = validate_disk(len(remap), 3, compacted)
        first = True
    except ValueError:
        first, edges = False, None
    second = independent_disk_gate(b, masks, owners)
    if first != second:
        raise ValueError("two distinct filled triangular-disk topology implementations disagree")
    if not first:
        return None
    return {
        "consecutive_original_boundary_owners": owners,
        "actual_patch_face_indices": sorted(indices),
        "actual_patch_faces": masks, "actual_enclosed_nonowner_labels": interior,
        "all_other_possible_nonowner_labels": [v for v in range(b, 26) if v not in interior],
        "maximum_original_nonowners_outside_patch": 26-b-len(interior),
        "six_distinct_original_outside_nonowners_required": 6,
        "exact_patch_vertices": len(vertices), "exact_patch_edges": edges,
        "exact_patch_faces": len(masks),
        "proper_subset_of_present_faces": len(indices) < len(row["faces"]),
    }


def patches(row):
    triangles = [tuple(v for v in range(row["next"]) if mask & (1 << v)) for mask in row["faces"]]
    if any(len(face) != 3 for face in triangles) or len(set(triangles)) != len(triangles):
        raise ValueError("malformed original triangular prefix")
    sides = defaultdict(list)
    for index, face in enumerate(triangles):
        for edge in combinations(face, 2):
            sides[edge].append(index)
    if any(len(incident) > 2 for incident in sides.values()):
        raise ValueError("nonmanifold original source prefix")
    found = []
    for base in range(row["B"]):
        owners = [base, (base+1) % row["B"], (base+2) % row["B"]]
        perimeter = set(combinations(sorted(owners), 2))
        anchors = [tuple(sorted(owners[:2])), tuple(sorted(owners[1:]))]
        if any(len(sides[edge]) != 1 for edge in anchors) or not perimeter <= set(sides):
            continue
        # Edge-based flood, independent of the older prebuilt dual-adjacency scan.
        seed = sides[anchors[0]][0]
        selected, queue = {seed}, [seed]
        for index in queue:
            for edge in combinations(triangles[index], 2):
                if edge in perimeter:
                    continue
                for neighbor in sides[edge]:
                    if neighbor not in selected:
                        selected.add(neighbor)
                        queue.append(neighbor)
        certificate = patch_certificate(row, owners, selected)
        if certificate is not None:
            found.append(certificate)
    return found


def shadow_case_distributions(row, patch):
    b = row["B"]
    inside = set(patch["actual_enclosed_nonowner_labels"])
    outside = set(range(b, 26))-inside
    result = []
    for m in range(b+9, 27):
        capacities = Counter()
        for shadows in combinations(range(b, 26), 26-m):
            available = len(outside-set(shadows))
            if available >= 6:
                raise ValueError("a shadow-placement case allows six original outsiders")
            capacities[available] += 1
        result.append({
            "original_irredundant_physical_disks": m, "shadow_labels_count": 26-m,
            "all_shadow_label_placements_checked": sum(capacities.values()),
            "placements_by_original_nonowners_available_outside_patch":
                {str(number): capacities[number] for number in sorted(capacities)},
        })
    return result
