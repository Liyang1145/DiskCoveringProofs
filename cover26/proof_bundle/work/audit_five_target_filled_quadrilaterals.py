"""Actual current28 mathematical scan; NOT geometry/current admission."""

from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path

from audit_prefix_origin import validate_disk
import verify_conditional_force_stage as binding


U = F(234701, 1000000)


def targets():
    r, h = 1-2*U, F(1, 2)-U
    # Coordinates mean (sqrt(3)*x_coefficient,y).
    points = [(F(0), F(0)), (F(0), r), (-r/2, r/2),
              (-r/2, -r/2), (F(0), -r)]
    distances = [3*(a[0]-b[0])**2+(a[1]-b[1])**2 for a, b in combinations(points, 2)]
    if (
        min(distances) != r*r or min(distances) <= 4*U*U or h <= U
        or any(x > 0 or 3*x*x+y*y > r*r for x, y in points)
        or F(7, 4)**2 <= 3
    ):
        raise ValueError("quadrilateral five-target exact projection/distance scope failed")
    return {
        "targets_sqrt3_x_coefficient_and_y": [[str(x), str(y)] for x, y in points],
        "exact_core_radius": str(r), "exact_minimum_squared_target_distance": str(min(distances)),
        "exact_polygon_projection_lower": str(h), "exact_projection_margin_above_U": str(h-U),
        "five_DISTINCT_ORIGINAL_outside_nonowners_required": 5,
    }


def independent_disk(b, masks, owners):
    triangles = [tuple(v for v in range(26) if mask & (1 << v)) for mask in masks]
    if not triangles or any(len(face) != 3 for face in triangles) or len(set(triangles)) != len(triangles):
        return None
    vertices = {v for face in triangles for v in face}
    if vertices & set(range(b)) != set(owners):
        return None
    perimeter = {tuple(sorted((owners[i], owners[(i+1) % 4]))) for i in range(4)}
    sides, at_vertex = defaultdict(list), defaultdict(list)
    for index, face in enumerate(triangles):
        for edge in combinations(face, 2):
            sides[edge].append(index)
        for vertex in face:
            at_vertex[vertex].append(face)
    if (
        any(len(incident) not in (1, 2) for incident in sides.values())
        or {edge for edge, incident in sides.items() if len(incident) == 1} != perimeter
        or len(vertices)-len(sides)+len(triangles) != 1
    ):
        return None
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
        return None
    for vertex in vertices:
        link = defaultdict(set)
        for face in at_vertex[vertex]:
            left, right = [v for v in face if v != vertex]
            link[left].add(right)
            link[right].add(left)
        if vertex in owners:
            position = owners.index(vertex)
            ends = {owners[(position-1) % 4], owners[(position+1) % 4]}
        else:
            ends = set()
        if (
            {v for v, neighbors in link.items() if len(neighbors) == 1} != ends
            or any(len(neighbors) not in (1, 2) for neighbors in link.values())
        ):
            return None
        start = next(iter(link))
        reached, queue = {start}, [start]
        for v in queue:
            for w in link[v]-reached:
                reached.add(w)
                queue.append(w)
        if reached != set(link):
            return None
    return len(sides)


def patches(row, independent_locator=False):
    b = row["B"]
    triangles = [tuple(v for v in range(row["next"]) if mask & (1 << v)) for mask in row["faces"]]
    sides = defaultdict(list)
    for index, face in enumerate(triangles):
        for edge in combinations(face, 2):
            sides[edge].append(index)
    result = []
    for base in range(b):
        owners = [(base+offset) % b for offset in range(4)]
        perimeter = {tuple(sorted((owners[i], owners[(i+1) % 4]))) for i in range(4)}
        anchors = [tuple(sorted((owners[i], owners[i+1]))) for i in range(3)]
        closing = tuple(sorted((owners[0], owners[-1])))
        if any(len(sides[edge]) != 1 for edge in anchors) or not sides[closing]:
            continue
        if independent_locator:
            dual = [set() for _ in triangles]
            for edge, incident in sides.items():
                if edge != closing and len(incident) == 2:
                    left, right = incident
                    dual[left].add(right)
                    dual[right].add(left)
            start = sides[anchors[1]][0]
            selected, queue = {start}, [start]
            for index in queue:
                for neighbor in dual[index]-selected:
                    selected.add(neighbor)
                    queue.append(neighbor)
        else:
            start = sides[anchors[0]][0]
            selected, queue = {start}, [start]
            for index in queue:
                for edge in combinations(triangles[index], 2):
                    if edge not in perimeter:
                        for neighbor in sides[edge]:
                            if neighbor not in selected:
                                selected.add(neighbor)
                                queue.append(neighbor)
        masks = [row["faces"][index] for index in sorted(selected)]
        vertices = {v for index in selected for v in triangles[index]}
        inner = sorted(vertices-set(range(b)))
        if vertices & set(range(b)) != set(owners) or 26-b-len(inner) >= 5:
            continue
        if independent_locator:
            edge_count = independent_disk(b, masks, owners)
        else:
            remap = {v: i for i, v in enumerate(owners+inner)}
            mapped = [sum(1 << remap[v] for v in vertices if mask & (1 << v)) for mask in masks]
            try:
                edge_count = validate_disk(len(remap), 4, mapped)
            except ValueError:
                edge_count = None
        if edge_count is None:
            continue
        result.append({
            "consecutive_original_boundary_owners": owners,
            "actual_patch_face_indices": sorted(selected), "actual_patch_faces": masks,
            "actual_enclosed_nonowner_labels": inner,
            "maximum_all_remaining_original_nonowner_slots": 26-b-len(inner),
            "five_distinct_original_nonowners_outside_required": 5,
            "exact_patch_edges": edge_count, "exact_patch_vertices": len(vertices),
            "exact_patch_faces": len(masks), "proper_subset_of_present_faces": len(selected) < len(triangles),
        })
    return result


def main():
    output = Path("outputs/n26-current28-five-target-filled-quadrilateral-mathematical-scan-v1.json")
    if output.exists():
        raise FileExistsError(output)
    source_path = Path("outputs/n26-conditional-force-stage-v28-sparse-v1/FRONTIER.json")
    six_path = Path("outputs/n26-current28-six-target-filled-ear-mathematical-scan-v1.json")
    source, six = binding.read(source_path), binding.read(six_path)
    six_indexes = {row["actual_source_index"] for row in six["results"]}
    paths = [source_path, six_path, Path(__file__),
             Path("work/n26-five-target-filled-quadrilateral-proof.md"),
             Path("work/n26-embedded-dual-and-corner-starring-bridge-proof.md"),
             Path("work/audit_prefix_origin.py")]
    digests = {str(path): binding.sha(path) for path in paths}
    target_result = targets()
    results, new_indexes = [], []
    for index, row in enumerate(source["pending_states"]):
        first, second = patches(row), patches(row, independent_locator=True)
        if first != second:
            raise AssertionError("two distinct quadrilateral locators/topology checks disagree")
        if first:
            if row["terminal"]:
                raise AssertionError("raw complete candidate/competitor claimed impossible")
            results.append({
                "actual_source_index": index, "B": row["B"], "prefix": row["prefix"],
                "actual_source_state": row, "filled_quadrilateral_certificates": first,
                "already_in_six_target_triangular_rule": index in six_indexes,
            })
            if index not in six_indexes:
                new_indexes.append(index)
        if (index+1) % 1000 == 0:
            print(json.dumps({"five_target_quad_actual_source_rows_scanned": index+1,
                              "qualifying_prefixes": len(results), "additional_over_six_triangles": len(new_indexes),
                              "formal_payments": 0}), flush=True)
    if any(binding.sha(path) != digest for path, digest in digests.items()):
        raise ValueError("quadrilateral actual source/proof changed")
    union = six_indexes | {row["actual_source_index"] for row in results}
    report = {
        "schema": "N26-current28-five-target-filled-quadrilateral-mathematical-scan-v1",
        "verified": False, "input_sha256": digests, "exact_five_target_identity_result": target_result,
        "results": results, "entire_actual_source_rows_scanned": len(source["pending_states"]),
        "qualifying_whole_quadrilateral_prefixes": len(results),
        "additional_over_six_target_triangular_rule_NOT_accepted": len(new_indexes),
        "additional_actual_source_indexes": new_indexes,
        "additional_family_counts": dict(Counter(str(source["pending_states"][i]["B"]) for i in new_indexes)),
        "union_with_six_triangular_rule_NOT_accepted": len(union),
        "prospective_union_frontier_NOT_current": len(source["pending_states"])-len(union),
        "complete_original_prefix_reconstruction_and_geometry_admission_STILL_required": True,
        "actual_formal_frontier_STILL": 11183, "candidate_whole_roots_STILL": 25,
        "new_formal_geometric_payments": 0, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_five_target_quad_mathematical_scan_completed": True,
        "qualifying_quad_prefixes": len(results), "additional_over_six_triangles": len(new_indexes),
        "prospective_union_frontier_NOT_current": len(source["pending_states"])-len(union),
        "formal_payments": 0, "candidate_whole_roots_removed": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
