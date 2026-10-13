"""Actual-source mathematical scan for proper filled boundary-ear patches.

No accepted frontier or geometry receipt is produced or modified.
"""

from collections import Counter, defaultdict
from itertools import combinations
import json
from pathlib import Path

from audit_n26_closed_ear_core_capacity import ear_patch
from test_n26_closed_ear_core_capacity import independent_patch
import verify_conditional_force_stage as binding


def patches(row):
    b, count = row["B"], row["next"]
    triangles = [tuple(v for v in range(count) if mask & (1 << v)) for mask in row["faces"]]
    if any(len(face) != 3 for face in triangles) or len(set(triangles)) != len(triangles):
        raise ValueError("actual prefix contains malformed or duplicate triangles")
    edges = defaultdict(list)
    for index, face in enumerate(triangles):
        for edge in combinations(face, 2):
            edges[edge].append(index)
    if any(len(incident) > 2 for incident in edges.values()):
        raise ValueError("actual source is not a triangular surface prefix")
    result = []
    for base in range(b):
        owners = [base, (base+1) % b, (base+2) % b]
        perimeter = set(combinations(sorted(owners), 2))
        anchor_edges = [tuple(sorted(owners[:2])), tuple(sorted(owners[1:]))]
        if any(len(edges[edge]) != 1 for edge in anchor_edges) or not perimeter <= set(edges):
            continue
        dual = [set() for _ in triangles]
        for edge, incident in edges.items():
            if edge not in perimeter and len(incident) == 2:
                left, right = incident
                dual[left].add(right)
                dual[right].add(left)
        selected, queue = {edges[anchor_edges[0]][0]}, [edges[anchor_edges[0]][0]]
        for index in queue:
            for neighbor in dual[index]-selected:
                selected.add(neighbor)
                queue.append(neighbor)
        incidence = Counter(edge for index in selected for edge in combinations(triangles[index], 2))
        if {edge for edge, hits in incidence.items() if hits == 1} != perimeter:
            continue
        vertices = {v for index in selected for v in triangles[index]}
        if vertices & set(range(b)) != set(owners):
            continue
        interior = sorted(vertices-set(range(b)))
        if len(interior) < 26-b-3:
            continue
        # Preserve owner labels. Only the local nonowner labels are compacted
        # for the existing two distinct disk-topology implementations.
        remap = {v: v for v in owners}
        remap.update({v: b+offset for offset, v in enumerate(interior)})
        local = {
            "B": b, "next": b+len(interior),
            "faces": [sum(1 << remap[v] for v in triangles[index]) for index in sorted(selected)],
        }
        first, second = ear_patch(local), independent_patch(local)
        if first != second:
            raise ValueError("distinct closed-disk patch implementations disagree")
        if first is None:
            continue
        result.append({
            "consecutive_original_boundary_owners": owners,
            "actual_patch_face_indices": sorted(selected),
            "actual_patch_faces": [row["faces"][index] for index in sorted(selected)],
            "actual_enclosed_nonowner_labels": interior,
            "all_other_possible_nonowner_labels": [v for v in range(b, 26) if v not in interior],
            "maximum_original_nonowners_outside_patch": 26-b-len(interior),
            "four_distinct_original_outside_nonowners_required": 4,
            "independently_checked_compacted_patch": first,
            "proper_subset_of_present_faces": len(selected) < len(triangles),
        })
    return result


def main():
    output = Path("outputs/n26-current28-general-filled-boundary-ear-mathematical-scan-v1.json")
    if output.exists():
        raise FileExistsError(output)
    folder = Path("outputs/n26-current28-closed-ear-source-geometry-v1")
    source_path = folder/"SOURCE-FRONTIER.json"
    source = binding.read(source_path)
    old_ledger = binding.read(folder/"LOWER-LEDGER.json")
    old_indexes = {row["source_index"] for row in old_ledger}
    paths = [source_path, folder/"LOWER-LEDGER.json", folder/"MANIFEST.json", Path(__file__),
             Path("work/n26-general-filled-boundary-ear-capacity-proof.md"),
             Path("work/audit_n26_closed_ear_core_capacity.py"),
             Path("work/test_n26_closed_ear_core_capacity.py")]
    digests = {str(path): binding.sha(path) for path in paths}
    results = []
    for index, row in enumerate(source["pending_states"]):
        found = patches(row)
        if found:
            if row["terminal"]:
                raise AssertionError("a retained complete candidate/competitor was claimed impossible")
            results.append({
                "actual_source_index": index, "B": row["B"], "prefix": row["prefix"],
                "actual_source_state": row, "filled_ear_patch_certificates": found,
                "already_in_original643_entire_present_ear_ledger": index in old_indexes,
            })
        if (index+1) % 1000 == 0:
            print(json.dumps({"general_filled_ear_actual_states_scanned": index+1,
                              "qualifying_whole_prefixes": len(results),
                              "formal_nodes_removed": 0}), flush=True)
    indexes = {row["actual_source_index"] for row in results}
    if not old_indexes <= indexes:
        raise AssertionError("general filled patch scan lost an old whole-ear obstruction")
    if any(binding.sha(path) != digest for path, digest in digests.items()):
        raise ValueError("general filled-ear mathematical inputs changed")
    new_indexes = indexes-old_indexes
    report = {
        "schema": "N26-current28-general-filled-boundary-ear-mathematical-scan-v1",
        "verified": False, "input_sha256": digests, "results": results,
        "entire_actual_current28_source_states_scanned": len(source["pending_states"]),
        "actual_qualifying_whole_prefixes": len(results),
        "original_entire_present_ear_prefixes_retained": len(old_indexes),
        "additional_proper_patch_whole_prefixes_NOT_accepted": len(new_indexes),
        "additional_actual_source_indexes": sorted(new_indexes),
        "qualifying_family_counts": dict(Counter(str(row["B"]) for row in results)),
        "additional_family_counts": dict(Counter(str(source["pending_states"][i]["B"]) for i in new_indexes)),
        "two_distinct_disk_topology_tests_agreed_for_each_claimed_patch": True,
        "complete_original_prefix_and_geometry_admission_NOT_performed_by_this_scan": True,
        "current_formal_frontier_STILL": 11183, "candidate_whole_roots_STILL": 25,
        "new_formal_geometric_payments": 0, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "general_filled_patch_scan_completed": True,
        "qualifying_whole_prefixes": len(results), "additional_proper_patch_prefixes": len(new_indexes),
        "formal_geometric_payments": 0, "candidate_whole_roots_removed": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
