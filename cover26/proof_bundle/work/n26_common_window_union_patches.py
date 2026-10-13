"""NEW full owner-subset polygons and common-window label unions."""

from collections import defaultdict
from itertools import combinations

from audit_prefix_origin import validate_disk
from n26_midarc_filled_patches import independent_disk_gate
from n26_sharp_shifted_core_filled_patches import REQUIRED, target_gate


def rotate_code(owners):
    return min(tuple(owners[i:]+owners[:i]) for i in range(len(owners)))


def owner_cycles(b, sides, independent=False):
    edges = set(sides)
    found = set()
    for start in range(b):
        window = [(start+offset) % b for offset in range(8)]
        if independent:
            for size in range(3, 9):
                for tail in combinations(range(1, 8), size-1):
                    owners = [start]+[window[offset] for offset in tail]
                    if all(tuple(sorted((owners[i], owners[(i+1) % size]))) in edges
                           for i in range(size)):
                        found.add(rotate_code(owners))
        else:
            def extend(offsets):
                if len(offsets) >= 3 and tuple(sorted((start, window[offsets[-1]]))) in edges:
                    found.add(rotate_code([window[offset] for offset in offsets]))
                for offset in range(offsets[-1]+1, 8):
                    if tuple(sorted((window[offsets[-1]], window[offset]))) in edges:
                        extend(offsets+[offset])
            extend([0])
    return sorted(found)


def filled_patches(row, independent=False):
    b, count = row["B"], row["next"]
    masks = row["faces"]
    if b not in (14, 15, 16, 17) or not b <= count <= 26:
        raise ValueError("common-window source changed original owner/label scope")
    if any(type(mask) is not int or not 0 < mask < 1 << count for mask in masks):
        raise ValueError("common-window source has invalid face labels")
    faces = [tuple(i for i in range(count) if mask >> i & 1) for mask in masks]
    if any(len(face) != 3 for face in faces) or len(faces) != len(set(faces)):
        raise ValueError("common-window source has malformed/repeated triangles")
    sides = defaultdict(list)
    for index, face in enumerate(faces):
        for edge in combinations(face, 2):
            sides[edge].append(index)
    if any(len(values) > 2 for values in sides.values()):
        raise ValueError("common-window source has a nonmanifold edge")
    patches, seen = [], set()
    for owners_tuple in owner_cycles(b, sides, independent):
        owners = list(owners_tuple)
        perimeter = [tuple(sorted((owners[i], owners[(i+1) % len(owners)])))
                     for i in range(len(owners))]
        blocked = set(perimeter)
        if independent:
            dual = [set() for _ in faces]
            for edge, incident in sides.items():
                if edge not in blocked and len(incident) == 2:
                    left, right = incident
                    dual[left].add(right)
                    dual[right].add(left)
            seeds = sides[perimeter[len(perimeter)//2]]
        else:
            seeds = sides[perimeter[0]]
        for seed in seeds:
            selected, todo = {seed}, [seed]
            for index in todo:
                if independent:
                    neighbors = dual[index]
                else:
                    neighbors = {neighbor for edge in combinations(faces[index], 2)
                                 if edge not in blocked for neighbor in sides[edge]}
                for neighbor in neighbors-selected:
                    selected.add(neighbor)
                    todo.append(neighbor)
            key = owners_tuple, tuple(sorted(selected))
            if key in seen:
                continue
            seen.add(key)
            chosen = [masks[index] for index in sorted(selected)]
            vertices = {v for index in selected for v in faces[index]}
            inside = sorted(vertices-set(range(b)))
            if not inside or vertices.intersection(range(b)) != set(owners):
                continue
            if independent:
                edge_count = independent_disk_gate(b, chosen, owners)
            else:
                permutation = {v: i for i, v in enumerate(owners+inside)}
                compact = [sum(1 << permutation[v] for v in vertices if mask >> v & 1)
                           for mask in chosen]
                try:
                    edge_count = validate_disk(len(permutation), len(owners), compact)
                except ValueError:
                    edge_count = None
            if edge_count is None:
                continue
            patches.append({
                "outer_original_boundary_owners": owners,
                "actual_patch_face_indices": sorted(selected), "actual_patch_faces": chosen,
                "actual_enclosed_nonowner_labels": inside,
                "exact_patch_vertices": len(vertices), "exact_patch_edges": edge_count,
                "exact_patch_faces": len(chosen),
            })
    return sorted(patches, key=lambda patch: (
        patch["outer_original_boundary_owners"], patch["actual_patch_face_indices"]))


def obstructions(row, patches):
    b = row["B"]
    result = []
    for size, need in REQUIRED.items():
        for start in range(b):
            owners = [(start+j) % b for j in range(size)]
            allowed = set(owners)
            selected = [index for index, patch in enumerate(patches)
                        if set(patch["outer_original_boundary_owners"]) <= allowed]
            inside = sorted({v for index in selected
                             for v in patches[index]["actual_enclosed_nonowner_labels"]})
            available = 26-b-len(inside)
            if available < need:
                result.append({
                    "actual_consecutive_original_owner_window": owners,
                    "window_length": size, "selected_filled_patch_indices": selected,
                    "actual_UNION_of_enclosed_nonowner_labels": inside,
                    "maximum_all_original_nonowner_slots_outside_UNION": available,
                    "required_DISTINCT_ORIGINAL_nonowners_outside_UNION": need,
                    "multiple_filled_patches_used": len(selected) > 1,
                    "nonconsecutive_outer_polygon_used": any(
                        len(patches[index]["outer_original_boundary_owners"]) < size for index in selected),
                })
    return result


def select(obstructions):
    return max(obstructions, key=lambda item: (
        item["required_DISTINCT_ORIGINAL_nonowners_outside_UNION"]
        - item["maximum_all_original_nonowner_slots_outside_UNION"],
        -item["window_length"]))
