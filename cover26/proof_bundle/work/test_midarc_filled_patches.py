"""Independent entire original-prefix/count controls for NEW midarc mathematics.

Uses the independent face-dual/link locator and independently written exact
target comparisons. This remains mathematical DATA, not geometry/current/
final acceptance or a complete n26 proof.
"""

from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
import n26_force as force
import n26_midarc_filled_patches as rule
import n26_six_target_filled_ears as family
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-current28-midarc-filled-patches-independent-controls-v1.json")
    if output.exists():
        raise FileExistsError(output)
    scan_path = Path("outputs/n26-current28-midarc-filled-patches-mathematical-scan-v1.json")
    producer = binding.read(scan_path)
    digests = dict(producer["input_sha256"])
    digests.update({
        str(scan_path): binding.sha(scan_path), __file__: binding.sha(__file__),
        rule.__file__: binding.sha(rule.__file__), force.__file__: binding.sha(force.__file__),
    })
    for text, digest in digests.items():
        if binding.sha(text) != digest:
            raise ValueError("midarc producer/input changed before independent reconstruction")
    source_path = Path("outputs/n26-conditional-force-stage-v28-sparse-v1/FRONTIER.json")
    parent_path = Path("outputs/n26-twenty-eighth-conditional-current-audit-v28-sparse-v1-strict-with-owned8-scope.json")
    final_path = Path("outputs/n26-twenty-eighth-conditional-final-digest-recheck-v28-sparse-v1-strict-with-owned8.json")
    constants_path = Path("outputs/n26-new-scope-v1/CONSTANTS.json")
    parent, final = binding.read(parent_path), binding.read(final_path)
    if (
        final["current_audit_sha256"] != binding.sha(parent_path)
        or parent["files"].get(linux(source_path)) != binding.sha(source_path)
        or parent["Rstar_conditional_frontier_pending_subtrees"] != 11183
        or parent["radius_scope"] != binding.SCOPE
        or parent["global_optimality_proved"] is not False
    ):
        raise ValueError("midarc mathematical baseline lost actual completed current/source pair")
    family.family_gate(binding.read(constants_path))
    for path in (parent_path, final_path, constants_path, Path(family.__file__)):
        digests[str(path)] = binding.sha(path)
    source = binding.read(source_path)
    records = {row["actual_source_index"]: row for row in producer["results"]}
    if len(records) != len(producer["results"]):
        raise ValueError("midarc source-prefix ownership duplicated")
    references = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D)
                  for b in (14, 15, 16, 17)}
    for reference in references.values():
        reference.children = lru_cache(None)(reference.children)
    seen, matched, cases, selected_counts = set(), [], 0, Counter()
    for index, row in enumerate(source["pending_states"]):
        key = row["B"], tuple(row["prefix"])
        if key in seen:
            raise ValueError("midarc mathematical source repeats a prefix")
        seen.add(key)
        reference = references[row["B"]]
        state = reference.resolve(key[1])
        if {"B": row["B"], **reference.entry(key[1], state, reference.children(state))} != row:
            raise ValueError("midarc ENTIRE original source-prefix reconstruction differs")
        patches = rule.patches(row, independent_locator=True)
        if bool(patches) != (index in records):
            raise ValueError("midarc independent full-source patch classification differs")
        if patches:
            recorded = records[index]
            selected = max(patches, key=lambda patch: (
                patch["required_DISTINCT_ORIGINAL_outside_nonowners"]
                - patch["maximum_all_original_nonowner_slots_outside"],
                -patch["outer_cycle_length"],
            ))
            if (
                row["terminal"] or recorded["actual_source_state"] != row
                or recorded["all_qualifying_filled_patches"] != patches
                or recorded["selected_strongest_filled_patch"] != selected
            ):
                raise ValueError("midarc independent patch/state/terminal ownership differs")
            outside = set(range(row["B"], 26))-set(selected["actual_enclosed_nonowner_labels"])
            need = {3: 7, 4: 6, 5: 5, 6: 5}[selected["outer_cycle_length"]]
            for m in range(row["B"]+9, 27):
                for originals in combinations(range(row["B"], 26), m-row["B"]):
                    if len(outside.intersection(originals)) >= need:
                        raise ValueError("midarc original/shadow case allows the required outside disks")
                    cases += 1
            matched.append(index)
            selected_counts[str(selected["outer_cycle_length"])] += 1
        if (index+1) % 1000 == 0:
            print(json.dumps({
                "midarc_independent_original_prefixes_reconstructed": index+1,
                "qualifying_prefixes": len(matched), "formal_payments": 0,
            }), flush=True)
    if any((b, prefix[:size]) in seen for b, prefix in seen for size in range(len(prefix))):
        raise ValueError("midarc source prefix ancestry overlap")
    u, r = F(234701, 1000000), 1-2*F(234701, 1000000)
    if not (u < F(1, 4) and F(7, 4)**2 > 3 and 0 < F(1054, 625)**2 < 3):
        raise ValueError("independent original-arc and triangular half-angle comparisons fail")
    exact = {}
    for k in (3, 4, 5, 6):
        if k == 3:
            points = [(F(0), F(0)), (F(0), r), (r/2, r/2),
                      (r/2, -r/2), (F(0), -r), (-r/2, -r/2), (-r/2, r/2)]
            x_factor, y_factor, cosine, xmax = 3, 1, F(24, 25), 7*r/8
        elif k == 4:
            points = [(F(0), F(0)), (r/2, r/2), (r/2, -r/2),
                      (-r/2, r/2), (-r/2, -r/2), (-r, F(0))]
            x_factor, y_factor, cosine, xmax = 1, 3, F(4, 5), r/2
        else:
            points = [(F(0), F(0)), (F(0), r), (-r/2, r/2),
                      (-r/2, -r/2), (F(0), -r)]
            x_factor, y_factor = 3, 1
            cosine, xmax = (F(7, 10) if k == 5 else F(1, 2)), F(0)
        pairs = [x_factor*(a[0]-b[0])**2+y_factor*(a[1]-b[1])**2
                 for a, b in combinations(points, 2)]
        margin = cosine-2*u-xmax
        if (
            min(pairs) != r*r or min(pairs) <= 4*u*u or margin <= 0
            or any(x_factor*x*x+y_factor*y*y > r*r for x, y in points)
            or (k == 4 and 4*cosine*cosine >= 3)
            or (k == 5 and 2*cosine*cosine >= 1)
            or producer["exact_seven_six_five_target_inequalities"][str(k)][
                "exact_patch_to_target_horizontal_margin_above_U"] != str(margin)
        ):
            raise ValueError("independent exact midarc target comparison differs")
        exact[str(k)] = {
            "exact_minimum_squared_target_distance": str(min(pairs)),
            "exact_horizontal_margin_above_U": str(margin),
            "required_distinct_original_nonowners": len(points),
        }
    rejected = []
    exemplar = records[matched[0]]["selected_strongest_filled_patch"]
    owners, masks, b = (
        exemplar["consecutive_original_boundary_owners"], exemplar["actual_patch_faces"],
        records[matched[0]]["B"],
    )
    for name, altered_masks, altered_owners in (
        ("missing-face-not-a-filled-disk", masks[1:], owners),
        ("duplicate-face-not-a-disk", masks+masks[:1], owners),
        ("wrong-outer-owner-cycle", masks, [*owners[:-1], (owners[-1]+2) % b]),
    ):
        if rule.independent_disk_gate(b, altered_masks, altered_owners) is not None:
            raise AssertionError("invalid midarc topology accepted: " + name)
        rejected.append(name)
    for k in (3, 4, 5, 6):
        for name, kwargs in (
            ("nonstrict-quarter-radius", {"u": F(1, 4)}),
            ("duplicated-core-target", {"points": [
                *[(F(value[0]), F(value[1])) for value in
                  producer["exact_seven_six_five_target_inequalities"][str(k)]["exact_target_coefficients"]][:-1],
                (F(0), F(0)),
            ]}),
        ):
            try:
                rule.target_gate(k, **kwargs)
            except ValueError:
                rejected.append(str(k) + ":" + name)
            else:
                raise AssertionError("invalid midarc target scope accepted")
    old_six = {row["actual_source_index"] for row in binding.read(
        Path("outputs/n26-current28-six-target-filled-ear-mathematical-scan-v1.json"))["results"]}
    old_quad = {row["actual_source_index"] for row in binding.read(
        Path("outputs/n26-current28-five-target-filled-quadrilateral-mathematical-scan-v1.json"))["results"]}
    if not old_six | old_quad <= set(matched):
        raise ValueError("independent midarc classification lost an old obstruction")
    if len(rejected) != 11:
        raise AssertionError("midarc mathematical controls incomplete")
    if any(binding.sha(path) != digest for path, digest in digests.items()):
        raise ValueError("midarc mathematical input/source/proof changed during independent reconstruction")
    report = {
        "schema": "N26-current28-midarc-filled-patches-independent-mathematical-controls-v1",
        "verified": False, "input_sha256": digests,
        "entire_original_source_prefixes_independently_reconstructed": len(source["pending_states"]),
        "independent_qualifying_whole_prefixes": len(matched),
        "independent_all_original_count_AND_shadow_label_cases_checked": cases,
        "independent_qualifying_family_counts": dict(Counter(
            str(source["pending_states"][index]["B"]) for index in matched)),
        "independent_selected_outer_cycle_length_counts": dict(selected_counts),
        "independent_exact_target_margin_results": exact,
        "additional_beyond_frozen_six_triangles_NOT_admitted": len(set(matched)-old_six),
        "additional_beyond_six_and_five_quad_union_NOT_admitted": len(set(matched)-(old_six | old_quad)),
        "prospective_frontier_NOT_current": len(source["pending_states"])-len(matched),
        "topology_and_strict_target_negative_controls_rejected": rejected,
        "all_raw_complete_terminals_and_unpaid_source_rows_retained": True,
        "NEW_geometry_own_publication_current_AND_final_STILL_required": True,
        "candidate_whole_roots_removed": 0, "new_formal_geometric_payments": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("input_sha256", "independent_exact_target_margin_results")}),
          flush=True)


if __name__ == "__main__":
    main()
