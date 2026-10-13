"""Independent whole-prefix replay and original-label check for six-target ears.

This is mathematical/control evidence only, NOT a geometry/current admission.
"""

from collections import Counter, defaultdict
from copy import deepcopy
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
import n26_force as force
import n26_six_target_filled_ears as rule
import verify_conditional_force_stage as binding


def independent_patches(row):
    b = row["B"]
    faces = [tuple(v for v in range(26) if mask & (1 << v)) for mask in row["faces"]]
    sides = defaultdict(list)
    for index, face in enumerate(faces):
        for edge in combinations(face, 2):
            sides[edge].append(index)
    result = []
    for first in range(b):
        owners = [first, (first+1) % b, (first+2) % b]
        outer_left = tuple(sorted(owners[:2]))
        outer_right = tuple(sorted(owners[1:]))
        diagonal = tuple(sorted((owners[0], owners[2])))
        if len(sides[outer_left]) != 1 or len(sides[outer_right]) != 1 or not sides[diagonal]:
            continue
        # Independent implementation: build the dual, cut ONLY the diagonal,
        # and seed from the OTHER outer boundary edge.
        dual = [set() for _ in faces]
        for edge, touching in sides.items():
            if edge != diagonal and len(touching) == 2:
                left, right = touching
                dual[left].add(right)
                dual[right].add(left)
        start = sides[outer_right][0]
        reached, queue = {start}, [start]
        for index in queue:
            for neighbor in dual[index]-reached:
                reached.add(neighbor)
                queue.append(neighbor)
        masks = [row["faces"][index] for index in sorted(reached)]
        vertices = {v for index in reached for v in faces[index]}
        interior = sorted(vertices-set(range(b)))
        if 26-b-len(interior) >= 6 or not rule.independent_disk_gate(b, masks, owners):
            continue
        patch_edges = {edge for index in reached for edge in combinations(faces[index], 2)}
        result.append({
            "consecutive_original_boundary_owners": owners,
            "actual_patch_face_indices": sorted(reached),
            "actual_patch_faces": masks, "actual_enclosed_nonowner_labels": interior,
            "all_other_possible_nonowner_labels": [v for v in range(b, 26) if v not in interior],
            "maximum_original_nonowners_outside_patch": 26-b-len(interior),
            "six_distinct_original_outside_nonowners_required": 6,
            "exact_patch_vertices": len(vertices), "exact_patch_edges": len(patch_edges),
            "exact_patch_faces": len(masks),
            "proper_subset_of_present_faces": len(reached) < len(faces),
        })
    return result


def independent_original_cases(row, patch):
    """Enumerate ORIGINAL sets, not the producer's shadow subsets."""
    b = row["B"]
    outside = set(range(b, 26))-set(patch["actual_enclosed_nonowner_labels"])
    distributions = []
    for m in range(b+9, 27):
        capacities = Counter()
        for originals in combinations(range(b, 26), m-b):
            remaining = len(outside.intersection(originals))
            if remaining >= 6:
                raise AssertionError("an original-disk label case can cover all six targets")
            capacities[remaining] += 1
        distributions.append({
            "original_irredundant_physical_disks": m, "shadow_labels_count": 26-m,
            "all_shadow_label_placements_checked": sum(capacities.values()),
            "placements_by_original_nonowners_available_outside_patch":
                {str(number): capacities[number] for number in sorted(capacities)},
        })
    return distributions


def main():
    output = Path("outputs/n26-current28-six-target-filled-ear-independent-controls-v1.json")
    if output.exists():
        raise FileExistsError(output)
    producer_path = Path("outputs/n26-current28-six-target-filled-ear-mathematical-scan-v1.json")
    producer = binding.read(producer_path)
    digests = dict(producer["input_sha256"])
    digests.update({str(producer_path): binding.sha(producer_path),
                    __file__: binding.sha(__file__), force.__file__: binding.sha(force.__file__)})
    for text, digest in digests.items():
        if binding.sha(text) != digest:
            raise ValueError("six-target source/proof/executor changed before independent replay")
    folder = Path("outputs/n26-current28-closed-ear-source-geometry-v1")
    manifest = binding.read(folder/"MANIFEST.json")
    parent_path, final_path = binding.local_path(manifest["parent_current"]), binding.local_path(manifest["parent_final"])
    parent, final = binding.read(parent_path), binding.read(final_path)
    if (
        binding.sha(parent_path) != manifest["parent_current_sha256"]
        or binding.sha(final_path) != manifest["parent_final_sha256"]
        or final["current_audit_sha256"] != manifest["parent_current_sha256"]
        or parent["Rstar_conditional_frontier_pending_subtrees"] != 11183
        or parent["candidate_angle_unresolved_closed_boxes"] != 25
    ):
        raise ValueError("six-target independent replay lost the actual completed source/current pair")
    source_path = binding.local_path(manifest["source_frontier"])
    source = binding.read(source_path)
    if (
        binding.sha(source_path) != manifest["source_frontier_sha256"]
        or source != binding.read(folder/"SOURCE-FRONTIER.json")
        or len(source["pending_states"]) != 11183
        or source["families"] != parent["Rstar_conditional_frontier_families"]
    ):
        raise ValueError("six-target replay substituted the actual source")
    rule.family_gate(binding.read(folder/"FAMILY-CONSTANTS.json"))
    expected = {item["actual_source_index"]: item for item in producer["results"]}
    if len(expected) != len(producer["results"]):
        raise AssertionError("six-target producer duplicated whole-prefix ownership")
    refs = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D)
            for b in (14, 15, 16, 17)}
    for reference in refs.values():
        reference.children = lru_cache(None)(reference.children)
    seen, matched, total_cases = set(), [], 0
    for index, row in enumerate(source["pending_states"]):
        key = row["B"], tuple(row["prefix"])
        if key in seen:
            raise AssertionError("six-target source has duplicate prefix ownership")
        seen.add(key)
        reference = refs[row["B"]]
        state = reference.resolve(key[1])
        if {"B": row["B"], **reference.entry(key[1], state, reference.children(state))} != row:
            raise AssertionError("six-target independent ENTIRE original-prefix reconstruction differs")
        found = independent_patches(row)
        if bool(found) != (index in expected):
            raise AssertionError("independent full-source filled-patch classification differs")
        if found:
            record = expected[index]
            selected = max(found, key=lambda patch: len(patch["actual_enclosed_nonowner_labels"]))
            distributions = independent_original_cases(row, selected)
            cases = sum(item["all_shadow_label_placements_checked"] for item in distributions)
            if (
                row["terminal"] or record["actual_source_state"] != row
                or record["all_qualifying_filled_patches"] != found
                or record["selected_strongest_filled_patch"] != selected
                or record["original_count_and_all_shadow_case_distributions"] != distributions
                or record["original_count_and_shadow_cases_checked"] != cases
            ):
                raise AssertionError("independent actual patch, original case or raw terminal differs")
            total_cases += cases
            matched.append(index)
        if (index+1) % 1000 == 0:
            print(json.dumps({"six_target_independent_original_prefixes_replayed": index+1,
                              "qualifying_prefixes": len(matched), "formal_geometric_payments": 0}), flush=True)
    if any((b, prefix[:length]) in seen for b, prefix in seen for length in range(len(prefix))):
        raise AssertionError("six-target source has overlapping ancestor/descendant prefixes")
    # Independent scalar exact-distance calculation. No floating trigonometry.
    u = F(234701, 1000000)
    radius = 1-2*u
    targets = [(F(0), F(0)), (radius/2, radius/2), (radius/2, -radius/2),
               (-radius/2, radius/2), (-radius/2, -radius/2), (-radius, F(0))]
    distances = [(a[0]-b[0])**2+3*(a[1]-b[1])**2 for a, b in combinations(targets, 2)]
    if (
        min(distances) != radius**2 or min(distances) <= 4*u*u
        or any(x*x+3*y*y > radius**2 for x, y in targets)
        or F(4, 5)-u-max(x for x, y in targets) != F(3, 10)
        or F(3, 10) <= u
        or len(matched) != 5546 or total_cases != 58916
        or len(matched) != producer["actual_qualifying_whole_prefixes"]
        or total_cases != producer["all_original_count_and_shadow_label_cases_checked"]
    ):
        raise AssertionError("independent exact target constants or complete case totals differ")
    negatives = []
    def rejected(name, call):
        try:
            call()
        except (ValueError, AssertionError, KeyError, TypeError):
            negatives.append(name)
        else:
            raise AssertionError("invalid six-target geometry/case control accepted: "+name)
    changed = list(targets)
    changed[1] = changed[0]
    rejected("duplicate-core-target", lambda: rule.target_gate(points=changed))
    rejected("only-five-distinct-targets", lambda: rule.target_gate(points=targets[:5]))
    changed = list(targets)
    changed[1] = (radius, F(0))
    rejected("rightmost-core-vertex-accessible-from-ear", lambda: rule.target_gate(points=changed))
    changed = list(targets)
    changed[1] = (radius*2, F(0))
    rejected("target-outside-the-covered-core", lambda: rule.target_gate(points=changed))
    changed = list(targets)
    changed[1] = (u/2, F(0))
    rejected("target-pair-coverable-by-one-disk", lambda: rule.target_gate(points=changed))
    rejected("non-strict-quarter-radius", lambda: rule.target_gate(u=F(1, 4)))
    constants = binding.read(folder/"FAMILY-CONSTANTS.json")
    for name, field, value in (
        ("eight-original-nonowners-hidden-by-shadows", "minimum_interior_cells", 8),
        ("external-eight-disk-theorem-hidden", "external_n8_theorem_assumed", False),
        ("original-owner-count-frame-replaced", "maximum_boundary_cells", 18),
    ):
        changed = dict(constants)
        changed[field] = value
        rejected(name, lambda changed=changed: rule.family_gate(changed))
    example = expected[matched[0]]["selected_strongest_filled_patch"]
    b = source["pending_states"][matched[0]]["B"]
    masks, owners = example["actual_patch_faces"], example["consecutive_original_boundary_owners"]
    if rule.independent_disk_gate(b, masks[1:], owners):
        raise AssertionError("open patch accepted as filled")
    negatives.append("one-missing-patch-face")
    if rule.independent_disk_gate(b, masks+ masks[:1], owners):
        raise AssertionError("duplicate face accepted")
    negatives.append("duplicate-patch-face")
    changed_owners = list(owners)
    changed_owners[-1] = (owners[0]+5) % b
    if rule.independent_disk_gate(b, masks, changed_owners):
        raise AssertionError("wrong original owner boundary accepted")
    negatives.append("wrong-original-boundary-owner")
    for text, digest in digests.items():
        if binding.sha(text) != digest:
            raise ValueError("six-target inputs changed during independent replay")
    report = {
        "schema": "N26-current28-six-target-filled-ear-independent-mathematical-controls-v1",
        "verified": False, "input_sha256": digests,
        "entire_original_source_prefixes_independently_reconstructed": len(source["pending_states"]),
        "all_source_prefixes_prefix_free_and_actual_parent_association_checked": True,
        "independent_qualifying_whole_prefixes": len(matched),
        "independent_qualifying_family_counts": dict(Counter(str(source["pending_states"][i]["B"]) for i in matched)),
        "independent_original_set_enumeration_cases_checked": total_cases,
        "independent_face_dual_diagonal_cut_and_other_boundary_seed_agreed": True,
        "independent_exact_minimum_squared_target_distance": str(min(distances)),
        "independent_exact_horizontal_ear_separation": "3/10",
        "six_target_and_original_owner_and_topology_negative_controls_rejected": negatives,
        "all_raw_complete_candidate_and_competitor_terminals_retained": True,
        "prospective_frontier_NOT_current": len(source["pending_states"])-len(matched),
        "actual_source_geometry_current_and_independent_final_STILL_required": True,
        "actual_formal_frontier_STILL": 11183, "candidate_whole_roots_STILL": 25,
        "new_formal_geometric_payments": 0, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "six_target_independent_entire_source_and_original_cases_completed": True,
        "source_prefixes": len(source["pending_states"]), "strict_conditional_prefixes": len(matched),
        "all_original_and_shadow_cases": total_cases, "actual_controls_rejected": len(negatives),
        "formal_geometric_payments": 0, "candidate_whole_roots_removed": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
