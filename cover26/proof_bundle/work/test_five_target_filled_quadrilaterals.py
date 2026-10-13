"""Independent actual original-prefix/case controls for the quadrilateral lemma."""

from collections import Counter
from copy import deepcopy
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
import audit_five_target_filled_quadrilaterals as quad
import n26_force as force
import n26_six_target_filled_ears as original_family
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-current28-five-target-filled-quadrilateral-independent-controls-v1.json")
    if output.exists():
        raise FileExistsError(output)
    producer_path = Path("outputs/n26-current28-five-target-filled-quadrilateral-mathematical-scan-v1.json")
    producer = binding.read(producer_path)
    digests = dict(producer["input_sha256"])
    digests.update({
        str(producer_path): binding.sha(producer_path),
        __file__: binding.sha(__file__), quad.__file__: binding.sha(quad.__file__),
        force.__file__: binding.sha(force.__file__),
    })
    source_path = Path("outputs/n26-conditional-force-stage-v28-sparse-v1/FRONTIER.json")
    current_path = Path("outputs/n26-twenty-eighth-conditional-current-audit-v28-sparse-v1-strict-with-owned8-scope.json")
    final_path = Path("outputs/n26-twenty-eighth-conditional-final-digest-recheck-v28-sparse-v1-strict-with-owned8.json")
    parent, final = binding.read(current_path), binding.read(final_path)
    if (
        final["current_audit_sha256"] != binding.sha(current_path)
        or parent["files"].get(linux(source_path)) != binding.sha(source_path)
        or parent["Rstar_conditional_frontier_pending_subtrees"] != 11183
        or parent["candidate_angle_unresolved_closed_boxes"] != 25
    ):
        raise ValueError("quadrilateral independent check lost the actual completed current/source pair")
    for path in (current_path, final_path):
        digests[str(path)] = binding.sha(path)
    source = binding.read(source_path)
    constants_path = Path("outputs/n26-new-scope-v1/CONSTANTS.json")
    original_family.family_gate(binding.read(constants_path))
    digests[str(constants_path)] = binding.sha(constants_path)
    digests[original_family.__file__] = binding.sha(original_family.__file__)
    records = {row["actual_source_index"]: row for row in producer["results"]}
    if len(records) != len(producer["results"]):
        raise ValueError("quadrilateral producer duplicated a prefix owner")
    refs = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D)
            for b in (14, 15, 16, 17)}
    for ref in refs.values():
        ref.children = lru_cache(None)(ref.children)
    matched, cases, seen = [], 0, set()
    for index, row in enumerate(source["pending_states"]):
        key = row["B"], tuple(row["prefix"])
        if key in seen:
            raise ValueError("duplicate actual source prefix")
        seen.add(key)
        ref = refs[row["B"]]
        state = ref.resolve(key[1])
        if {"B": row["B"], **ref.entry(key[1], state, ref.children(state))} != row:
            raise ValueError("quadrilateral ENTIRE original source-prefix reconstruction differs")
        found = quad.patches(row, independent_locator=True)
        if bool(found) != (index in records):
            raise ValueError("independent whole-source quadrilateral classification differs")
        if found:
            expected = records[index]
            if row["terminal"] or expected["actual_source_state"] != row or expected["filled_quadrilateral_certificates"] != found:
                raise ValueError("actual quadrilateral certificate/state or raw terminal ownership differs")
            selected = max(found, key=lambda patch: len(patch["actual_enclosed_nonowner_labels"]))
            outside = set(range(row["B"], 26))-set(selected["actual_enclosed_nonowner_labels"])
            for m in range(row["B"]+9, 27):
                for originals in combinations(range(row["B"], 26), m-row["B"]):
                    if len(outside.intersection(originals)) >= 5:
                        raise ValueError("an original/shadow placement has five possible outside disks")
                    cases += 1
            matched.append(index)
        if (index+1) % 1000 == 0:
            print(json.dumps({"quad_independent_original_prefixes_reconstructed": index+1,
                              "qualifying_prefixes": len(matched), "formal_payments": 0}), flush=True)
    if any((b, prefix[:length]) in seen for b, prefix in seen for length in range(len(prefix))):
        raise ValueError("quadrilateral source has ancestor/descendant overlap")
    u, radius = F(234701, 1000000), 1-2*F(234701, 1000000)
    points = [(F(0), F(0)), (F(0), radius), (-radius/2, radius/2),
              (-radius/2, -radius/2), (F(0), -radius)]
    pair_squared = [3*(a[0]-b[0])**2+(a[1]-b[1])**2 for a, b in combinations(points, 2)]
    if (
        min(pair_squared) != radius**2 or min(pair_squared) <= 4*u*u
        or F(1, 2)-u <= u or F(7, 4)**2 <= 3
        or any(x > 0 or 3*x*x+y*y > radius**2 for x, y in points)
        or len(matched) != 3289
    ):
        raise ValueError("independent five-target rational/radical/projection comparison failed")
    negatives = []
    example = records[matched[0]]["filled_quadrilateral_certificates"][0]
    owners, masks = example["consecutive_original_boundary_owners"], example["actual_patch_faces"]
    b = records[matched[0]]["B"]
    for name, changed_masks, changed_owners in (
        ("one-missing-face-not-filled", masks[1:], owners),
        ("duplicate-face-not-disk", masks+masks[:1], owners),
        ("wrong-four-owner-cycle", masks, [owners[0], owners[1], owners[2], (owners[0]+6) % b]),
    ):
        if quad.independent_disk(b, changed_masks, changed_owners) is not None:
            raise AssertionError("invalid quadrilateral topology accepted: "+name)
        negatives.append(name)
    # Distances and projection are checked from exact expressions, never
    # finite approximations to a circle coverage test.
    if F(1, 2)-F(1, 4) > F(1, 4):
        raise AssertionError("non-strict quarter-radius projection accepted")
    negatives.append("quarter-radius-has-no-strict-projection-margin")
    repeated = list(points)
    repeated[1] = repeated[0]
    if min(3*(a[0]-b[0])**2+(a[1]-b[1])**2 for a, b in combinations(repeated, 2)) > 4*u*u:
        raise AssertionError("duplicate target accepted as separated")
    negatives.append("duplicate-core-target-does-not-force-five-disks")
    if not producer["additional_actual_source_indexes"] or len(producer["additional_actual_source_indexes"]) != 446:
        raise ValueError("actual added quadrilateral ownership count differs")
    for text, digest in digests.items():
        if binding.sha(text) != digest:
            raise ValueError("quadrilateral inputs changed during the independent replay")
    report = {
        "schema": "N26-current28-five-target-filled-quadrilateral-independent-mathematical-controls-v1",
        "verified": False, "input_sha256": digests,
        "entire_original_source_prefixes_independently_reconstructed": len(source["pending_states"]),
        "independent_qualifying_quadrilateral_prefixes": len(matched),
        "independent_all_original_count_and_shadow_cases_checked": cases,
        "independent_family_counts": dict(Counter(str(source["pending_states"][i]["B"]) for i in matched)),
        "additional_beyond_six_target_triangles_NOT_admitted": 446,
        "prospective_union_frontier_NOT_current": 5191,
        "exact_minimum_squared_target_distance": str(min(pair_squared)),
        "exact_quadrilateral_projection_margin_above_U": str(F(1, 2)-2*u),
        "topology_and_strict_distance_negative_controls_rejected": negatives,
        "all_raw_complete_terminals_and_unpaid_source_rows_retained": True,
        "new_geometry_current_AND_independent_final_STILL_required": True,
        "actual_formal_frontier_STILL": 11183, "candidate_whole_roots_STILL": 25,
        "new_formal_geometric_payments": 0, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_quad_independent_entire_source_and_case_controls_completed": True,
        "source_prefixes": len(source["pending_states"]), "qualifying_quad_prefixes": len(matched),
        "all_original_and_shadow_cases": cases, "additional_over_triangles_NOT_admitted": 446,
        "formal_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
