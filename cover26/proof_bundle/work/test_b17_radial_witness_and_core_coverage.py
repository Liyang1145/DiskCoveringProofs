"""Independent exact witness replay and elementary core-circle arithmetic."""

from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
import n26_force as force
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-b17-independent-radial-witness-core-coverage-v1.json")
    if output.exists():
        raise FileExistsError(output)
    witness_path = Path("outputs/n26-b17-eight-actual-radial-relaxation-witnesses-v1.json")
    proof_path = Path("work/n26-b17-inner-core-circle-coverage-proof.md")
    record = binding.read(witness_path)
    digests = dict(record["input_sha256"])
    digests.update({str(witness_path): binding.sha(witness_path),
                    str(proof_path): binding.sha(proof_path), __file__: binding.sha(__file__)})
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("exact witness input association changed")
    u, rcore, kappa = F(234701, 1000000), F(265299, 500000), F(165933607, 207000000)
    annulus_lower, annulus_upper = 1-3*u, 1-u
    if not (rcore == 1-2*u and rcore > 2*u and annulus_lower > u):
        raise AssertionError("core-circle/annulus separation arithmetic failed")
    chord_squared_margin = rcore**2-4*u**2
    if chord_squared_margin <= 0:
        raise AssertionError("regular-hexagon/one-sixth-turn chord is not strictly separated")
    radius = F(record["same_root_lower_radius_strictly_above_all_present_rods"])
    arcs = force.load_trig(Path("outputs/n26-original-candidate-arithmetic-context-v1"))[0]
    reference = OriginReference(26, 17, "dfs", caps=force.CAPS, scale=force.D)
    states, rods, results = 0, 0, []
    for row in record["results"]:
        source = row["actual_source_state"]
        prefix = tuple(source["prefix"])
        state = reference.resolve(prefix)
        if source != {"B": 17, **reference.entry(prefix, state, reference.children(state))}:
            raise AssertionError("independent exact narrowed source reconstruction failed")
        b, introduced, faces = 17, source["next"], source["faces"]
        turns = list(map(F, row["exact_anchor_turns"]))
        free = [list(map(F, p)) for p in row["exact_rational_free_points"]]
        spec = {"N": 26, "B": b, "next": introduced, "faces": faces}
        matrix = force.angular_domain(spec)
        if any(turns[j]-turns[i] > F(matrix[i][j], force.D)
               for i in range(b) for j in range(b)):
            raise AssertionError("independent witness angle-domain control failed")
        if not 1-turns[16] < F(9, 200) or sum(v*v for v in free[0]) > kappa**2:
            raise AssertionError("independent inward boundary-owner/short-gap control failed")
        # Different ordering: reconstruct boundary-center incidents first,
        # then present triangle incidents, rather than calling rod_graph.
        edges = [(i, b+i) for i in range(b)]+[(i, b+(i+1) % b) for i in range(b)]
        edges += [(b+introduced+k, b+i) for k, mask in enumerate(faces)
                  for i in range(introduced) if mask & (1 << i)]
        squared = []
        for uvertex, vvertex in edges:
            if uvertex < b:
                cosine, sine = arcs.sincos_turn(turns[uvertex])
                target = free[vvertex-b]
                bound = F(0)
                for interval, value in zip((cosine, sine), target):
                    a, c = F(interval[0], arcs.SCALE)-value, F(interval[1], arcs.SCALE)-value
                    bound += max(a*a, c*c)
            else:
                bound = sum((a-c)**2 for a, c in zip(free[uvertex-b], free[vvertex-b]))
            if bound >= radius**2:
                raise AssertionError("independent necessary-rod point is not strictly below radius")
            squared.append(bound)
        if (squared != list(map(F, row["exact_all_present_rod_squared_upper_bounds"]))
                or radius**2-max(squared) != F(row["exact_minimum_rod_squared_margin_below_Rstar_lower"])):
            raise AssertionError("independent exact all-present-rod bound mismatch")
        # Unintroduced nonowner labels are assigned the same explicitly
        # specified point as center1. No future rods/faces are claimed.
        nonowners = free[b:introduced]+[free[1][:] for _ in range(26-introduced)]
        if len(nonowners) != 9:
            raise AssertionError("at-most-nine nonowner scope changed")
        norm_squares = [sum(v*v for v in point) for point in nonowners]
        annulus_count = sum(annulus_lower**2 < t < annulus_upper**2 for t in norm_squares)
        origin_owners = sum(t <= u**2 for t in norm_squares)
        if annulus_count != 0 or origin_owners != 0:
            raise AssertionError("witness's absent actual core coverage was not reproduced")
        if min(sum(v*v for v in p) for p in free[:introduced]+[free[1]]) <= radius**2:
            raise AssertionError("independent exact origin noncoverage failed")
        states += 1
        rods += len(edges)
        results.append({
            "actual_prefix": source["prefix"], "actual_present_rods_rechecked": len(edges),
            "strictly_below_Rstar_present_rod_model_plus_inward_owner_feasible": True,
            "actual_witness_nonowner_centers_in_required_annulus": annulus_count,
            "actual_witness_nonowners_covering_origin_even_at_U": origin_owners,
            "new_core_coverage_condition_rejects_this_point_NOT_the_whole_source_state": True,
        })
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("witness/core proof input changed during independent checking")
    report = {
        "schema": "N26-B17-independent-exact-relaxation-witness-core-coverage-v1",
        "verified": False, "input_sha256": digests, "results": results,
        "actual_narrowed_source_states_independently_reconstructed": states,
        "actual_present_necessary_rods_independently_rechecked": rods,
        "exact_core_circle_radius": str(rcore),
        "exact_conservative_open_nonowner_annulus": [str(annulus_lower), str(annulus_upper)],
        "exact_core_circle_one_sixth_turn_chord_squared_margin_above_2U_squared": str(chord_squared_margin),
        "exact_annulus_lower_radius_margin_above_origin_cover_radius_U": str(annulus_lower-u),
        "minimum_positive_length_core_circle_nonowner_disks": 7,
        "minimum_additional_distinct_origin_cover_nonowner_disks": 1,
        "minimum_total_nonowner_disks": 8,
        "maximum_core_circle_nonowner_disks_at_B17_and_N26": 8,
        "six_regular_hexagon_vertices_plus_origin_need_seven_distinct_nonowners": True,
        "elementary_geometric_arc_and_finite_closed_union_argument_in_proof_note": True,
        "no_new_external_theorem_used_in_this_core_circle_lemma": True,
        "existing_relaxation_has_feasible_points_so_its_whole_states_cannot_be_paid": True,
        "new_core_coverage_lemma_NOT_yet_admitted_into_current_enumeration": True,
        "actual_source_whole_states_excluded": 0, "new_geometric_payments": 0,
        "candidate_whole_roots_removed": 0,
        "source_forests_histories_and_ledgers_UNMODIFIED": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: report[key] for key in (
        "actual_narrowed_source_states_independently_reconstructed",
        "actual_present_necessary_rods_independently_rechecked",
        "minimum_positive_length_core_circle_nonowner_disks",
        "minimum_additional_distinct_origin_cover_nonowner_disks",
        "actual_source_whole_states_excluded")}), flush=True)


if __name__ == "__main__":
    main()
