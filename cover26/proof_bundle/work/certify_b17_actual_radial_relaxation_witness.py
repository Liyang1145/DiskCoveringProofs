"""Exact feasible rod/radial witnesses for the eight actual narrowed prefixes.

These are deliberately NOT disk covers: the origin is independently uncovered.
Thus the tested present-rod/inward-owner relaxation cannot exclude these states.
"""

from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
import n26_b17_radial_origin_energy as radial
import n26_force as force
import verify_conditional_force_stage as binding


def norm(point):
    return sum(v*v for v in point)


def squared_interval_difference(interval, value):
    a, b = interval[0]-value, interval[1]-value
    return max(a*a, b*b)


def main():
    output = Path("outputs/n26-b17-eight-actual-radial-relaxation-witnesses-v1.json")
    if output.exists():
        raise FileExistsError(output)
    audit_path = Path("outputs/n26-b17-short-gap-actual-domain-audit-v1.json")
    stage = Path("outputs/n26-conditional-force-stage-v35-sparse-v1")
    source = stage/"FRONTIER.json"
    current_path = Path("outputs/n26-twenty-eighth-conditional-final-digest-recheck-v28-sparse-v1-strict-with-owned8.json")
    accepted = binding.read(stage/"VERIFIED.json")
    if (binding.sha(source) != accepted["files"]["FRONTIER.json"]
            or binding.sha(force.__file__) != accepted["files"]["n26_force.py"]):
        raise ValueError("actual accepted original model/domain changed")
    audit = binding.read(audit_path)
    wanted = {tuple(row["actual_source_prefix"]) for row in audit["results"]
              if row["exact_new_constraint_removes_an_old_angular_point"]}
    rows = [row for row in binding.read(source)["pending_states"]
            if row["B"] == 17 and tuple(row["prefix"]) in wanted]
    if len(rows) != 8:
        raise ValueError("not the original eight individually narrowed actual prefixes")
    arcs, trig_path = force.load_trig(Path("outputs/n26-original-candidate-arithmetic-context-v1"))
    radius = F(binding.read(current_path)["r_strict_interval"][0])
    paths = [audit_path, source, stage/"VERIFIED.json", current_path, Path(__file__),
             Path(force.__file__), Path(radial.__file__), Path(trig_path)]
    digests = {str(path): binding.sha(path) for path in paths}
    # Owner0's wrap gap and owners1/2 each get 1/50 turn. The fourteen
    # remaining gaps each get 47/700 turn; total is exactly one full turn.
    turns = [F(0), F(1, 50), F(1, 25)]
    turns += [F(1, 25)+F(47*(j-2), 700) for j in range(3, 17)]
    gaps = [1-turns[-1]]+[turns[j]-turns[j-1] for j in range(1, 17)]
    if sum(gaps) != 1 or gaps[0] != F(1, 50) or not gaps[0] < radial.ALPHA:
        raise AssertionError("explicit new inward-owner gap failed")
    anchor_intervals = []
    for turn in turns:
        c, s = arcs.sincos_turn(turn)
        anchor_intervals.append([[F(v, arcs.SCALE) for v in c],
                                 [F(v, arcs.SCALE) for v in s]])

    def rational_point(turn, distance):
        c, s = arcs.sincos_turn(turn)
        return [distance*F(sum(c), 2*arcs.SCALE),
                distance*F(sum(s), 2*arcs.SCALE)]

    centers = [rational_point(F(-1, 100), F(4, 5)),
               rational_point(F(1, 100), F(4, 5)),
               rational_point(F(3, 100), F(4, 5))]
    centers += [rational_point((turns[j]+turns[j-1])/2, F(999, 1000))
                for j in range(3, 17)]
    centers += [centers[1][:] for _ in range(9)]
    if not norm(centers[0]) <= radial.KAPPA**2 or any(norm(p) >= 1 for p in centers):
        raise AssertionError("exact inward-owner/unit-disk rational center control failed")
    origin_margin = min(norm(p) for p in centers)-radius**2
    if origin_margin <= 0:
        raise AssertionError("explicit relaxation is unexpectedly a cover at the origin")
    reference = OriginReference(26, 17, "dfs", caps=force.CAPS, scale=force.D)
    results = []
    for row in rows:
        prefix = tuple(row["prefix"])
        state = reference.resolve(prefix)
        if row != {"B": 17, **reference.entry(prefix, state, reference.children(state))}:
            raise ValueError("actual narrowed prefix failed independent reconstruction")
        spec = {"N": 26, "B": 17, "next": row["next"], "faces": row["faces"]}
        matrix = force.angular_domain(spec)
        if any(turns[j]-turns[i] > F(matrix[i][j], force.D)
               for i in range(17) for j in range(17)):
            raise AssertionError("explicit rational angle point violates actual original domain")
        if any(any(i > 2 for i in range(17) if face & (1 << i)) for face in row["faces"]):
            raise AssertionError("actual present witness has an unexpected boundary center")
        vertices, edges = force.rod_graph(spec)
        free = centers[:row["next"]]+[centers[1][:] for _ in row["faces"]]
        if len(free)+17 != vertices:
            raise AssertionError("actual partial free-vertex count changed")
        squared_upper = []
        for u, v in edges:
            if u < 17:
                bound = sum(squared_interval_difference(anchor_intervals[u][d], free[v-17][d])
                            for d in range(2))
            else:
                bound = sum((free[u-17][d]-free[v-17][d])**2 for d in range(2))
            squared_upper.append(bound)
        margin = radius**2-max(squared_upper)
        if margin <= 0:
            raise AssertionError("explicit feasible present-rod realization not strictly below Rstar")
        results.append({
            "actual_source_state": row,
            "exact_anchor_turns": list(map(str, turns)),
            "exact_cyclic_ownership_gaps_owner0_first": list(map(str, gaps)),
            "exact_rational_free_points": [[str(v) for v in point] for point in free],
            "actual_vertices": vertices, "actual_present_rods": len(edges),
            "exact_all_present_rod_squared_upper_bounds": list(map(str, squared_upper)),
            "exact_minimum_rod_squared_margin_below_Rstar_lower": str(margin),
            "exact_boundary_owner0_squared_norm_margin_below_K_squared":
                str(radial.KAPPA**2-norm(centers[0])),
            "exact_maximum_free_squared_norm": str(max(norm(p) for p in free)),
            "all_original_closed_angular_domain_constraints_checked": True,
            "new_inward_owner_and_strict_short_gap_constraint_satisfied": True,
            "origin_is_exactly_uncovered_by_all26centers": True,
            "origin_minimum_squared_distance_margin_above_Rstar_lower_squared": str(origin_margin),
            "only_necessary_relaxation_feasible_NOT_a_disk_cover": True,
        })
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("witness input/model changed during exact checking")
    report = {
        "schema": "N26-eight-actual-B17-new-radial-relaxation-exact-witnesses-v1",
        "verified": False, "input_sha256": digests, "results": results,
        "exact_feasible_current_present_rod_plus_radial_domain_witnesses": len(results),
        "same_root_lower_radius_strictly_above_all_present_rods": str(radius),
        "eight_selected_states_cannot_be_excluded_using_ONLY_this_necessary_model": True,
        "this_does_NOT_refute_true_cover_infeasibility_or_the_full_n26_goal": True,
        "continuous_disk_cover_or_global_counterexample_NOT_proved": True,
        "complete_actual_source_geometry_admission_NOT_performed": True,
        "source_forests_histories_and_ledgers_UNMODIFIED": True,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "exact_feasible_actual_present_rod_and_new_radial_domains": len(results),
        "all26center_points_leave_origin_uncovered": True,
        "using_ONLY_current_present_rods_and_radial_constraint_cannot_exclude_these8states": True,
        "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
