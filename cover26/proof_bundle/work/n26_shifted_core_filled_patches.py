"""NEW exact shifted-core geometry and fully filled 3..8-owner patches.

Mathematical DATA only: no frozen geometry/current receipt is modified.
"""

from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations

from audit_prefix_origin import validate_disk
from n26_midarc_filled_patches import independent_disk_gate


U = F(234701, 1000000)
REQUIRED = {3: 8, 4: 7, 5: 6, 6: 5, 7: 3, 8: 2}
COSINE_LOWER = {
    3: F(24, 25), 4: F(433, 500), 5: F(7, 10),
    6: F(1, 2), 7: F(1, 4), 8: F(0),
}


def target_points(k):
    if k == 4:
        return [(F(-3, 100), F(0)), (F(-3, 100), F(49, 100)),
                (F(-3, 100), F(-49, 100)), (F(197, 500), F(49, 200)),
                (F(197, 500), F(-49, 200)), (F(-227, 500), F(49, 200)),
                (F(-227, 500), F(-49, 200))]
    if k == 5:
        return [(F(-1, 50), F(0)), (F(9, 40), F(53, 125)),
                (F(9, 40), F(-53, 125)), (F(-53, 200), F(53, 125)),
                (F(-53, 200), F(-53, 125)), (F(-51, 100), F(0))]
    if k == 6:
        return [(F(0), F(0)), (F(0), F(1, 2)), (F(0), F(-1, 2)),
                (F(-43, 100), F(1, 4)), (F(-43, 100), F(-1, 4))]
    if k == 7:
        return [(F(-23, 100), F(47, 100)), (F(-23, 100), F(-47, 100)),
                (F(-13, 25), F(0))]
    if k == 8:
        return [(F(-47, 100), F(6, 25)), (F(-47, 100), F(-6, 25))]
    raise ValueError("three-owner obstruction uses a continuous disk, not eight sampled points")


def target_gate(k, u=U, points=None, disk_center=None, disk_radius=None):
    if k not in REQUIRED or not 0 < u < F(1, 4):
        raise ValueError("shifted-core rule requires k=3..8 and strict quarter-radius scope")
    if not (
        0 < F(1054, 625) and F(1054, 625)**2 < 3
        and 4*COSINE_LOWER[4]**2 < 3
        and 2*COSINE_LOWER[5]**2 < 1
        and F(7, 4)**2 > 3
    ):
        raise ValueError("shifted-core rational cosine comparisons failed")
    r, cosine = 1-2*u, COSINE_LOWER[k]
    common = {
        "consecutive_original_owners": k,
        "required_DISTINCT_ORIGINAL_outside_nonowners": REQUIRED[k],
        "exact_core_radius": str(r), "exact_cosine_rational_lower": str(cosine),
        "written_continuous_geometry_is_explicit_NOT_proved_by_this_scalar_gate": True,
    }
    if k == 3:
        center = F(-1, 40) if disk_center is None else F(disk_center)
        radius = F(1, 2) if disk_radius is None else F(disk_radius)
        if (
            points is not None or radius <= 0 or abs(center)+radius >= r
            or 2*u >= radius or cosine-2*u-center-radius <= 0
        ):
            raise ValueError("shifted continuous disk is accessible, outside core or seven-disk bound fails")
        return {
            **common, "mode": "continuous-shifted-disk-seven-cover-impossibility",
            "exact_target_disk_center": [str(center), "0"],
            "exact_target_disk_radius": str(radius),
            "exact_core_containment_radial_margin": str(r-abs(center)-radius),
            "exact_radius_margin_above_two_U": str(radius-2*u),
            "exact_patch_to_target_horizontal_margin_above_U": str(cosine-2*u-center-radius),
            "continuous_seven_disk_circle_arc_proof_NOT_a_finite_target_test": True,
        }
    if disk_center is not None or disk_radius is not None:
        raise ValueError("point obstruction does not accept an unproved disk substitution")
    expected = target_points(k)
    points = expected if points is None else points
    if len(points) != REQUIRED[k] or len(set(points)) != REQUIRED[k]:
        raise ValueError("wrong number of distinct shifted targets")
    norms = [x*x+y*y for x, y in points]
    pairs = [(a[0]-b[0])**2+(a[1]-b[1])**2 for a, b in combinations(points, 2)]
    xmax = max(x for x, y in points)
    margin = cosine-2*u-xmax
    if max(norms) >= r*r or min(pairs) <= 4*u*u or margin <= 0:
        raise ValueError("shifted targets are not strictly interior, separated and patch-inaccessible")
    return {
        **common, "mode": "separated-exact-rational-shifted-targets",
        "exact_target_points": [[str(x), str(y)] for x, y in points],
        "exact_maximum_squared_target_norm": str(max(norms)),
        "exact_core_squared_containment_margin": str(r*r-max(norms)),
        "exact_minimum_squared_pair_distance": str(min(pairs)),
        "exact_squared_pair_margin_above_four_U_squared": str(min(pairs)-4*u*u),
        "exact_target_x_maximum": str(xmax),
        "exact_patch_to_target_horizontal_margin_above_U": str(margin),
    }


def patches(row, independent_locator=False):
    b, next_label = row["B"], row["next"]
    if b not in (14, 15, 16, 17) or not b <= next_label <= 26:
        raise ValueError("shifted-core source changed original owner/label scope")
    masks = row["faces"]
    if any(not isinstance(mask, int) or mask <= 0 or mask >= 1 << next_label for mask in masks):
        raise ValueError("shifted-core source face has an invalid label mask")
    faces = [tuple(v for v in range(next_label) if mask & (1 << v)) for mask in masks]
    if any(len(face) != 3 for face in faces) or len(set(faces)) != len(faces):
        raise ValueError("shifted-core source has malformed triangular faces")
    sides = defaultdict(list)
    for index, face in enumerate(faces):
        for edge in combinations(face, 2):
            sides[edge].append(index)
    if any(len(incident) > 2 for incident in sides.values()):
        raise ValueError("shifted-core source has a nonmanifold edge")
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
            chosen = [masks[index] for index in sorted(selected)]
            vertices = {v for index in selected for v in faces[index]}
            inside = sorted(vertices-set(range(b)))
            if vertices & set(range(b)) != set(owners) or 26-b-len(inside) >= required:
                continue
            if independent_locator:
                edge_count = independent_disk_gate(b, chosen, owners)
            else:
                remap = {v: i for i, v in enumerate(owners+inside)}
                compact = [sum(1 << remap[v] for v in vertices if mask & (1 << v))
                           for mask in chosen]
                try:
                    edge_count = validate_disk(len(remap), k, compact)
                except ValueError:
                    edge_count = None
            if edge_count is None:
                continue
            results.append({
                "consecutive_original_boundary_owners": owners,
                "outer_cycle_length": k,
                "actual_patch_face_indices": sorted(selected), "actual_patch_faces": chosen,
                "actual_enclosed_nonowner_labels": inside,
                "maximum_all_original_nonowner_slots_outside": 26-b-len(inside),
                "required_DISTINCT_ORIGINAL_outside_nonowners": required,
                "exact_patch_vertices": len(vertices), "exact_patch_edges": edge_count,
                "exact_patch_faces": len(chosen),
                "proper_subset_of_present_faces": len(selected) < len(faces),
            })
    return results
