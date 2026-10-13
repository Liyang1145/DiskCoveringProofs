"""Independent complete actual-source replay for the CONDITIONAL closed-ear rule."""

from collections import Counter, defaultdict
from copy import deepcopy
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
import n26_force as force
import verify_conditional_force_stage as binding


def independent_patch(row):
    b, count = row["B"], row["next"]
    triangles = [tuple(v for v in range(count) if mask & (1 << v)) for mask in row["faces"]]
    if (count > 26 or 26-count > 3 or any(len(face) != 3 for face in triangles)
            or len(set(triangles)) != len(triangles)
            or len(triangles) != 2*(count-b)+1):
        return None
    used = {v for face in triangles for v in face}
    owners = used & set(range(b))
    if len(owners) != 3 or used-set(range(b)) != set(range(b, count)):
        return None
    bases = [v for v in owners if owners == {v, (v+1) % b, (v+2) % b}]
    if len(bases) != 1:
        return None
    base = bases[0]
    edges, vertex_faces = defaultdict(list), defaultdict(list)
    for index, face in enumerate(triangles):
        for edge in combinations(face, 2):
            edges[edge].append(index)
        for vertex in face:
            vertex_faces[vertex].append(face)
    expected_boundary = set(combinations(sorted(owners), 2))
    if ({edge for edge, incident in edges.items() if len(incident) == 1} != expected_boundary
            or any(len(incident) not in (1, 2) for incident in edges.values())
            or len(used)-len(edges)+len(triangles) != 1):
        return None
    # Independent dual-face connectivity explicitly rules out a closed
    # disconnected component with Euler characteristic zero.
    dual = [set() for _ in triangles]
    for incident in edges.values():
        if len(incident) == 2:
            left, right = incident
            dual[left].add(right)
            dual[right].add(left)
    seen, queue = {0}, [0]
    for face_index in queue:
        for neighbor in dual[face_index]-seen:
            seen.add(neighbor)
            queue.append(neighbor)
    if len(seen) != len(triangles):
        return None
    # Manifold vertex links: one path on each of the three boundary
    # vertices, one circle on every enclosed nonowner.
    for vertex in used:
        link = defaultdict(set)
        for face in vertex_faces[vertex]:
            left, right = [v for v in face if v != vertex]
            link[left].add(right)
            link[right].add(left)
        endpoints = {v for v, neighbors in link.items() if len(neighbors) == 1}
        expected = owners-{vertex} if vertex in owners else set()
        if endpoints != expected or any(len(neighbors) not in (1, 2) for neighbors in link.values()):
            return None
        start = next(iter(link))
        seen, queue = {start}, [start]
        for v in queue:
            for w in link[v]-seen:
                seen.add(w)
                queue.append(w)
        if seen != set(link):
            return None
    return {
        "consecutive_boundary_triangle": [base, (base+1) % b, (base+2) % b],
        "exact_patch_vertices": len(used), "exact_patch_edges": len(edges),
        "exact_patch_faces": len(triangles),
        "all_introduced_nonowners_enclosed_by_embedded_patch": list(range(b, count)),
        "unintroduced_nonowners_at_most": 26-count,
        "four_distinct_outside_ear_core_point_owners_required": 4,
        "exact_missing_outside_ear_owner_count": 4-(26-count),
    }


def main():
    output = Path("outputs/n26-closed-ear-core-capacity-independent-audit-v1.json")
    if output.exists():
        raise FileExistsError(output)
    pilot_path = Path("outputs/n26-closed-ear-core-capacity-actual-state-audit-v1.json")
    pilot = binding.read(pilot_path)
    digests = dict(pilot["input_sha256"])
    digests.update({str(pilot_path): binding.sha(pilot_path), __file__: binding.sha(__file__)})
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("closed-ear producer/source/proof changed")
    source = Path("outputs/n26-conditional-force-stage-v35-sparse-v1/FRONTIER.json")
    rows = binding.read(source)["pending_states"]
    recorded = {row["actual_stage35_source_index"]: row for row in pilot["results"]}
    if len(recorded) != len(pilot["results"]):
        raise AssertionError("duplicate actual closed-ear prefix ownership")
    refs = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D) for b in (14, 15, 16, 17)}
    for reference in refs.values():
        reference.children = lru_cache(None)(reference.children)
    matched, rejected_controls = [], []
    for index, row in enumerate(rows):
        patch = independent_patch(row)
        if patch is None:
            if index in recorded:
                raise AssertionError("independent topology rejected a claimed actual ear")
            continue
        if index not in recorded:
            raise AssertionError("independent full actual-source scan found an omitted qualifying ear")
        expected = recorded[index]
        if expected["actual_source_state"] != row or expected["closed_disk_patch_certificate"] != patch:
            raise AssertionError("actual source/closed-patch certificate association changed")
        ref, prefix = refs[row["B"]], tuple(row["prefix"])
        state = ref.resolve(prefix)
        if {"B": row["B"], **ref.entry(prefix, state, ref.children(state))} != row:
            raise AssertionError("independent original actual-prefix reconstruction failed")
        matched.append(index)
        if not rejected_controls:
            for name in ("missing-face", "duplicate-face", "false-introduced-count", "nonconsecutive-boundary"):
                changed = deepcopy(row)
                if name == "missing-face":
                    changed["faces"].pop()
                elif name == "duplicate-face":
                    changed["faces"][-1] = changed["faces"][0]
                elif name == "false-introduced-count":
                    changed["next"] += 1
                else:
                    old = patch["consecutive_boundary_triangle"]
                    # Relabel the third boundary vertex to a distant unused
                    # boundary vertex; all topology is kept, but not the
                    # indispensable consecutive-owner geometry hypothesis.
                    replacement = (old[0]+5) % row["B"]
                    if replacement in old:
                        raise AssertionError("negative boundary control did not choose a new label")
                    changed["faces"] = [(mask & ~(1 << old[2])) | (
                        (1 << replacement) if mask & (1 << old[2]) else 0)
                        for mask in changed["faces"]]
                if independent_patch(changed) is not None:
                    raise AssertionError("independent ear checker accepted "+name)
                rejected_controls.append(name)
    if set(matched) != set(recorded):
        raise AssertionError("independent scan failed exact actual-prefix cover association")
    u, h, rcore = F(234701, 1000000), F(4, 5)-F(234701, 1000000), 1-2*F(234701, 1000000)
    # Independent rational square comparisons for the two radical clauses,
    # plus exact geometric-distance separation for all four core points.
    sine_threshold_square_margin = F(7, 4)**2-3
    cosine_projection_square_margin = F(3, 4)-F(4, 5)**2
    if min(sine_threshold_square_margin, cosine_projection_square_margin, h-u,
           rcore-2*u, rcore**2-4*u**2) <= 0 or not u < F(1, 4):
        raise AssertionError("whole-ear/core capacity geometric constants are not strict")
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("closed-ear source/proof changed during independent replay")
    report = {
        "schema": "N26-closed-ear-core-capacity-independent-conditional-source-audit-v1",
        "verified": False, "input_sha256": digests, "producer_sha256": digests[str(pilot_path)],
        "entire_actual_stage35_source_states_independently_scanned": len(rows),
        "actual_closed_ear_prefixes_independently_reconstructed_and_checked": len(matched),
        "actual_source_indexes": matched,
        "independent_conditional_obstructions_by_boundary_family": dict(
            Counter(str(rows[index]["B"]) for index in matched)),
        "independent_conditional_obstructions_by_missing_nonowner_count": dict(
            Counter(str(26-rows[index]["next"]) for index in matched)),
        "independent_closed_disk_incidence_links_Euler_and_dual_connectivity_checked": True,
        "actual_negative_patch_and_consecutive_boundary_controls_rejected": rejected_controls,
        "exact_sin_pi_over12_comparison_radical_square_margin": str(sine_threshold_square_margin),
        "exact_cos_pi_over6_projection_comparison_square_margin": str(cosine_projection_square_margin),
        "exact_ear_projection_margin_above_U": str(h-u),
        "exact_four_core_targets_minimum_distance_margin_above_2U": str(rcore-2*u),
        "entire_geometric_prefix_infeasibility_UNDER_EMBEDDED_PHYSICAL_SOURCE_HYPOTHESIS_checked": True,
        "embedded_physical_simple_dual_and_m_less26_starring_admission_NOT_done": True,
        "frozen_geometric_reduction_proved": False,
        "original_below_Rstar_rod_relaxation_witnesses_remain_valid": True,
        "current_source_frontier_transport_nodes_removed": 0, "new_geometric_payments": 0,
        "candidate_whole_roots_removed": 0,
        "source_frozen_code_histories_ledgers_and_paid_leaves_UNMODIFIED": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: report[key] for key in (
        "entire_actual_stage35_source_states_independently_scanned",
        "actual_closed_ear_prefixes_independently_reconstructed_and_checked",
        "independent_conditional_obstructions_by_boundary_family",
        "independent_conditional_obstructions_by_missing_nonowner_count",
        "actual_negative_patch_and_consecutive_boundary_controls_rejected",
        "current_source_frontier_transport_nodes_removed", "new_geometric_payments")}), flush=True)


if __name__ == "__main__":
    main()
