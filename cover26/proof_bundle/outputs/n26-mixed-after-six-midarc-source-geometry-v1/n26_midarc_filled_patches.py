"""Exact NEW midarc target inequalities and filled 3/4/5/6-cycle recognition."""

from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations

from audit_prefix_origin import validate_disk


U = F(234701, 1000000)
REQUIRED = {3: 7, 4: 6, 5: 5, 6: 5}
COSINE_LOWER = {3: F(24, 25), 4: F(4, 5), 5: F(7, 10), 6: F(1, 2)}


def target_gate(k, u=U, points=None):
    if k not in REQUIRED or not 0 < u < F(1, 4):
        raise ValueError("midarc rule requires k=3..6 and a strict quarter-radius scope")
    if (
        F(1054, 625)**2 >= 3 or F(1054, 625) <= 0
        or 4*COSINE_LOWER[4]**2 >= 3
        or 2*COSINE_LOWER[5]**2 >= 1
        or F(7, 4)**2 <= 3
    ):
        raise ValueError("midarc exact half-angle/radical comparisons failed")
    r = 1-2*u
    if k == 3:
        # Actual point=(sqrt(3)*x_coefficient,y).
        expected = [(F(0), F(0)), (F(0), r), (r/2, r/2),
                    (r/2, -r/2), (F(0), -r), (-r/2, -r/2), (-r/2, r/2)]
        x_weight, y_weight, maximum_x_bound = 3, 1, 7*r/8
        coordinate_description = "sqrt3*x_coefficient,y"
    elif k == 4:
        # Actual point=(x,sqrt(3)*y_coefficient).
        expected = [(F(0), F(0)), (r/2, r/2), (r/2, -r/2),
                    (-r/2, r/2), (-r/2, -r/2), (-r, F(0))]
        x_weight, y_weight, maximum_x_bound = 1, 3, r/2
        coordinate_description = "x,sqrt3*y_coefficient"
    else:
        expected = [(F(0), F(0)), (F(0), r), (-r/2, r/2),
                    (-r/2, -r/2), (F(0), -r)]
        x_weight, y_weight, maximum_x_bound = 3, 1, F(0)
        coordinate_description = "sqrt3*x_coefficient,y"
    points = expected if points is None else points
    if len(points) != REQUIRED[k] or len(set(points)) != REQUIRED[k]:
        raise ValueError("midarc targets are not the required number of distinct points")
    pair_squared = [
        x_weight*(left[0]-right[0])**2+y_weight*(left[1]-right[1])**2
        for left, right in combinations(points, 2)
    ]
    maximum_x_coefficient = r/2 if k == 3 else (r/2 if k == 4 else F(0))
    margin = COSINE_LOWER[k]-2*u-maximum_x_bound
    if (
        any(x_weight*x*x+y_weight*y*y > r*r for x, y in points)
        or max(x for x, y in points) > maximum_x_coefficient
        or min(pair_squared) <= 4*u*u or margin <= 0
    ):
        raise ValueError("midarc targets are outside core, unseparated or accessible to the filled patch")
    return {
        "consecutive_original_owners": k,
        "required_DISTINCT_ORIGINAL_outside_nonowners": REQUIRED[k],
        "target_coordinate_description": coordinate_description,
        "exact_target_coefficients": [[str(x), str(y)] for x, y in points],
        "exact_core_radius": str(r), "exact_cosine_rational_lower": str(COSINE_LOWER[k]),
        "exact_minimum_squared_pair_distance": str(min(pair_squared)),
        "exact_squared_pair_margin_above_four_U_squared": str(min(pair_squared)-4*u*u),
        "exact_target_x_rational_upper": str(maximum_x_bound),
        "exact_patch_to_target_horizontal_margin_above_U": str(margin),
        "written_continuous_midarc_and_embedding_proof_STILL_explicit": True,
    }


def independent_disk_gate(b, masks, owners):
    """Independent Euler/incidence/dual/link topology; no validate_disk call."""
    faces = [tuple(v for v in range(26) if mask & (1 << v)) for mask in masks]
    if not faces or any(len(face) != 3 for face in faces) or len(set(faces)) != len(faces):
        return None
    vertices = {v for face in faces for v in face}
    if vertices & set(range(b)) != set(owners):
        return None
    perimeter = {tuple(sorted((owners[i], owners[(i+1) % len(owners)])))
                 for i in range(len(owners))}
    sides, at_vertex = defaultdict(list), defaultdict(list)
    for index, face in enumerate(faces):
        for edge in combinations(face, 2):
            sides[edge].append(index)
        for vertex in face:
            at_vertex[vertex].append(face)
    if (
        any(len(incident) not in (1, 2) for incident in sides.values())
        or {edge for edge, incident in sides.items() if len(incident) == 1} != perimeter
        or len(vertices)-len(sides)+len(faces) != 1
    ):
        return None
    dual = [set() for _ in faces]
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
    if len(reached) != len(faces):
        return None
    for vertex in vertices:
        link = defaultdict(set)
        for face in at_vertex[vertex]:
            left, right = [v for v in face if v != vertex]
            link[left].add(right)
            link[right].add(left)
        if vertex in owners:
            position = owners.index(vertex)
            ends = {owners[(position-1) % len(owners)], owners[(position+1) % len(owners)]}
        else:
            ends = set()
        if (
            {v for v, neighbors in link.items() if len(neighbors) == 1} != ends
            or any(len(neighbors) not in (1, 2) for neighbors in link.values())
        ):
            return None
        start = next(iter(link))
        reached, queue = {start}, [start]
        for vertex2 in queue:
            for neighbor in link[vertex2]-reached:
                reached.add(neighbor)
                queue.append(neighbor)
        if reached != set(link):
            return None
    return len(sides)


def patches(row, independent_locator=False):
    b = row["B"]
    faces = [tuple(v for v in range(row["next"]) if mask & (1 << v))
             for mask in row["faces"]]
    if any(len(face) != 3 for face in faces) or len(set(faces)) != len(faces):
        raise ValueError("midarc source has a malformed triangular face")
    sides = defaultdict(list)
    for index, face in enumerate(faces):
        for edge in combinations(face, 2):
            sides[edge].append(index)
    if any(len(incident) > 2 for incident in sides.values()):
        raise ValueError("midarc source has a nonmanifold edge")
    results = []
    for k, required in REQUIRED.items():
        for base in range(b):
            owners = [(base+offset) % b for offset in range(k)]
            perimeter = {tuple(sorted((owners[i], owners[(i+1) % k]))) for i in range(k)}
            anchors = [tuple(sorted((owners[i], owners[i+1]))) for i in range(k-1)]
            closing = tuple(sorted((owners[0], owners[-1])))
            if any(len(sides[edge]) != 1 for edge in anchors) or not sides[closing]:
                continue
            if independent_locator:
                dual = [set() for _ in faces]
                for edge, incident in sides.items():
                    if edge != closing and len(incident) == 2:
                        left, right = incident
                        dual[left].add(right)
                        dual[right].add(left)
                seed = sides[anchors[(k-1)//2]][0]
                selected, queue = {seed}, [seed]
                for index in queue:
                    for neighbor in dual[index]-selected:
                        selected.add(neighbor)
                        queue.append(neighbor)
            else:
                seed = sides[anchors[0]][0]
                selected, queue = {seed}, [seed]
                for index in queue:
                    for edge in combinations(faces[index], 2):
                        if edge not in perimeter:
                            for neighbor in sides[edge]:
                                if neighbor not in selected:
                                    selected.add(neighbor)
                                    queue.append(neighbor)
            masks = [row["faces"][index] for index in sorted(selected)]
            vertices = {v for index in selected for v in faces[index]}
            inner = sorted(vertices-set(range(b)))
            if vertices & set(range(b)) != set(owners) or 26-b-len(inner) >= required:
                continue
            if independent_locator:
                edge_count = independent_disk_gate(b, masks, owners)
            else:
                remap = {v: i for i, v in enumerate(owners+inner)}
                mapped = [sum(1 << remap[v] for v in vertices if mask & (1 << v))
                          for mask in masks]
                try:
                    edge_count = validate_disk(len(remap), k, mapped)
                except ValueError:
                    edge_count = None
            if edge_count is None:
                continue
            results.append({
                "consecutive_original_boundary_owners": owners,
                "outer_cycle_length": k,
                "actual_patch_face_indices": sorted(selected), "actual_patch_faces": masks,
                "actual_enclosed_nonowner_labels": inner,
                "maximum_all_original_nonowner_slots_outside": 26-b-len(inner),
                "required_DISTINCT_ORIGINAL_outside_nonowners": required,
                "exact_patch_vertices": len(vertices), "exact_patch_edges": edge_count,
                "exact_patch_faces": len(masks),
                "proper_subset_of_present_faces": len(selected) < len(faces),
            })
    return results
