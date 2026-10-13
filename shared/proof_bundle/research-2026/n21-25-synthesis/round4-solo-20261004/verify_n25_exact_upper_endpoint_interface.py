"""Fresh exact upper/local results, own radical radius, and real complete core.

The old 311883-node continuous core theorem and original complete-parent
transport are reused honestly, not claimed freshly replayed by this interface.
"""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
SYN = ROOT.parent
WORK = ROOT.parents[2]
sys.path.insert(0, str(SYN))
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from n25_algebraic_upper import Q2, R2, A2
from replay_n25_tight_domain import inputs
from group_catalog import validate

assert __debug__
UPPER = ROOT / "n25-own-exact-upper-fresh-v1"
LOCAL = ROOT / "n25-own-exact-endpoint-local-fresh-v1/REPORT.json"
OLDLOCAL = HIGH / "evidence/n25-endpoint-tight-isolation-gamma2000-resume1/REPORT.json"
CORE = ROOT / "n25-tight-core-fresh-exact-replay.json"
CANDIDATE = ROOT / "n25-B16-single-candidate-collar-closure-20261005-v1.json"
TRANSPORT = ROOT / "n25-B16-p115569-nonstrict1/VERIFIED.json"


def gate(upper, local, geometry, replay, candidate, transport):
    assert upper["verified"] and upper["actual_cover_radius_equals_r"]
    assert (upper["exact_nearest_anchors_checked"], upper["vertices"], upper["edges"],
            upper["triangles"], upper["boundary_caps"], upper["center_faces"]) == (16, 41, 104, 64, 16, 32)
    assert upper["radius_isolated_by"] == "exact quadratic-field squared comparisons; not decimal definition"
    assert upper["acceptance_source_sha256"] == sha(SYN / "n25_algebraic_upper.py")
    assert upper["geometry_sha256"] == sha(UPPER / "geometry.json")
    own = read(UPPER / "geometry.json")
    assert own["N"] == 25 and own["B"] == 16
    assert own["r_squared"] == geometry["t_Qsqrt2"] == R2.dump() == ["1", "-2/3"]
    assert own["a_squared"] == A2.dump() == ["2/3", "-1/3"]
    assert R2 == 1/(9+6*Q2(0, 1)) and R2.sign() > 0
    for lower, higher in (upper["r_strict_interval"],):
        assert (R2-Q2(F(lower)**2)).sign() > 0
        assert (Q2(F(higher)**2)-R2).sign() > 0
    assert local["verified"] and local["N"] == 25 and not local["entire_angle_domain_proved"]
    assert local["source_sha256"] == sha(HIGH / "n25_endpoint_tight_isolation.py")
    assert local["geometry_sha256"] == sha(HIGH / "evidence/n25-isolation-exact-resume1/rotated-geometry.json")
    assert [row["parameter_sign"] for row in local["cores"]] == [-1, 1]
    for row in local["cores"]:
        assert row["verified"] and row["positive_leading_principal_minors"] == 120
        assert row["first_failed_pivot"] is None
        assert (row["G"], row["core_nodes"], row["positive_rods"], row["gamma"]) == (120, 61, 92, 2000)
        assert len(row["principal_minor_binary_sha256"]) == 120
        assert (F(row["lambda"]), F(row["nu"]), F(row["anchor_radius"]),
                F(row["isolation_margin"])) == (F(1, 5000), F(21, 5000), F(1, 20), F(59, 2500000))
        assert F(row["lambda"])-2*row["gamma"]*F(row["nu"])**2*F(row["anchor_radius"])**2 == F(row["isolation_margin"])
        assert row["old_nodes_retained"][:41] == list(range(41))
        assert len(row["points_Qsqrt2"]) == 61 and len(row["edges"]) == 92 and len(row["faces"]) == 20
    assert replay["verified"] and replay["entire_angle_domain_proved"] and replay["paid_unpaid_partition_complete"]
    assert (replay["N"], replay["B"], replay["parameter_sign"], replay["nodes"], replay["pending_boxes"]) == (25, 16, -1, 311883, 0)
    assert replay["counts"] == {"SPLIT": 155941, "DUAL": 153567, "LOCAL": 2375}
    assert F(replay["minimum_force_margin"]) > 0 and F(replay["minimum_local_margin"]) > 0
    assert replay["source_sha256"] == sha(HIGH / "replay_n25_tight_domain.py")
    assert candidate["verified"] and candidate["complete_this_simple_hole_completion_family"]
    assert (candidate["N"], candidate["B"], candidate["full_completion_types"], candidate["strictly_excluded"],
            candidate["known_attaining_core_lower_paid"], candidate["pending_completions"]) == (25, 16, 91, 90, 1, 0)
    assert candidate["core_lower_radius"] == "1/(sqrt(6)+sqrt(3))"
    assert transport["verified"] and (transport["N"], transport["B"], transport["parent_index"]) == (25, 16, 115569)
    assert transport["entire_parent_outer_faces_literally_equal_not_proper_subgraph_or_count_only"]
    assert transport["all_simple_hole_completions_freshly_reenumerated_without_node_budget"]
    assert transport["actual_complete_parent_source_row_and_genuine_original_pending_snapshot_matched"]
    assert transport["old90_strict_and311883_node_core_math_theorem_reused_unchanged_not_fresh_replay_claim"]
    assert transport["not_a_strict_upper_radius_exclusion_of_the_attaining_parent"]
    assert transport["faces"] == candidate["collar_faces"]
    assert transport["candidate_theorem_sha256"] == sha(CANDIDATE)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    upper, local, replay, candidate, transport = map(read, (
        UPPER / "VERIFIED.json", LOCAL, CORE, CANDIDATE, TRANSPORT))
    geometrypath = HIGH / "evidence/n25-isolation-exact-resume1/rotated-geometry.json"
    geometry = read(geometrypath)
    gate(upper, local, geometry, replay, candidate, transport)
    assert LOCAL.read_bytes() == OLDLOCAL.read_bytes()
    constants, masks, _, bound, negative = inputs(-1)
    assert replay["input_sha256"] == bound
    treepath = HIGH / "evidence/n25-endpoint-negative-angle-tight-pruned-resume1.json.gz"
    assert replay["tree_sha256"] == sha(treepath)
    for key in ("points_Qsqrt2", "faces", "edges", "weights_Qsqrt2",
                "free_circle_multipliers_Qsqrt2", "old_nodes_retained"):
        assert local["cores"][0][key] == negative[key]
    groupspath = ROOT / "n25-B16-candidate-simple-hole-completions-20261005-v1/GROUPS.json"
    groups = read(groupspath)
    full = groups["groups"][candidate["attaining_group"]]
    assert (full["id"], full["centers"]) == (90, 25)
    validate(25, 16, masks, candidate["negative_endpoint_core_to_attaining_full_graph"], full["faces"])
    parentmaps = TRANSPORT.parent / "PARENT-TO-COMPLETIONS.json"
    assert sha(parentmaps) == transport["parent_to_completions_sha256"]
    maps = read(parentmaps)["all91_actual_complete_face_center_and_anchor_maps"]
    assert sorted(row["group"] for row in maps) == list(range(91))
    for row in maps:
        target = groups["groups"][row["group"]]
        validate(25, 16, candidate["collar_faces"], row["actual_parent_to_complete_type_map"], target["faces"])
    files = {}
    for relative, digest in candidate["files_relative_to_workspace"].items():
        path = (WORK / relative).resolve()
        assert path.is_relative_to(WORK) and sha(path) == digest
        files[str(path)] = digest
    for path in (
        Path(__file__), UPPER / "VERIFIED.json", UPPER / "geometry.json", LOCAL, OLDLOCAL,
        CORE, CANDIDATE, TRANSPORT, parentmaps, groupspath, treepath, geometrypath,
        SYN / "n25_algebraic_upper.py", HIGH / "n25_endpoint_tight_isolation.py",
        HIGH / "replay_n25_tight_domain.py", HIGH / "replay_n25_endpoint_domain.py",
        HIGH / "N25-STRESS-ENDPOINT-CORES.md", HIGH / "N25-STRESS-ENDPOINT-CORES-ADVANCE.md",
        ROOT / "N25-GLOBAL-SOURCE-PROOF-v1.md",
        ROOT / "n25-own-exact-family-budget-v1/VERIFIED.json"):
        files[str(path)] = sha(path)
    refused = []
    smalltransport = {k: v for k, v in transport.items() if k != "frozen_files"}
    smallcandidate = {k: v for k, v in candidate.items() if k != "files_relative_to_workspace"}
    for label, key, value in (
        ("upper", "verified", False), ("upper", "actual_cover_radius_equals_r", False),
        ("upper", "boundary_caps", 15), ("geometry", "t_Qsqrt2", ["1", "-1/3"]),
        ("local", "verified", False), ("replay", "pending_boxes", 1),
        ("replay", "entire_angle_domain_proved", False),
        ("candidate", "full_completion_types", 90), ("candidate", "known_attaining_core_lower_paid", 0),
        ("transport", "parent_index", 47808),
        ("transport", "entire_parent_outer_faces_literally_equal_not_proper_subgraph_or_count_only", False),
        ("transport", "not_a_strict_upper_radius_exclusion_of_the_attaining_parent", False)):
        wrong = dict(upper=upper, local=local, geometry=geometry, replay=replay,
                     candidate=smallcandidate, transport=smalltransport)
        wrong[label] = deepcopy(wrong[label])
        wrong[label][key] = value
        try:
            gate(**wrong)
        except (AssertionError, KeyError):
            refused.append(label+"-"+key)
        else:
            raise AssertionError("incorrect N25 same-root interface accepted")
    for field, value in (("gamma", 500), ("nu", "1/50"), ("positive_leading_principal_minors", 119),
                         ("anchor_radius", "1/50")):
        wrong = deepcopy(local)
        wrong["cores"][0][field] = value
        try:
            gate(upper, wrong, geometry, replay, smallcandidate, smalltransport)
        except (AssertionError, KeyError):
            refused.append("negative-core-"+field)
        else:
            raise AssertionError("incorrect endpoint local scope accepted")
    assert len(refused) == 16
    for path, digest in files.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N25-own-radical-exact-upper-fresh-endpoint-local-and-real-full-core-interface-v1",
        "N": 25, "exact_radius": "1/(sqrt(6)+sqrt(3))", "exact_radius_squared_Qsqrt2": ["1", "-2/3"],
        "same_exact_radius_not_approximate_decimal_or_other_order": True,
        "all_actual25_disk_closed_unit_disk_upper_freshly_exactly_recomputed": True,
        "both120_endpoint_local_principal_minors_and_perturbation_margins_freshly_recomputed": True,
        "fresh_local_report_identical_to_original_entire_angle_theorem_local_premise": True,
        "actual_full91_family_and_unique_full_core_all_center_anchor_and_face_maps_rechecked": True,
        "specified311883_node_entire_core_math_honestly_reused_unchanged_not_claimed_new_replay": True,
        "specified_core_lower_nonstrict_R_not_strict_U_and_not_all_competing_graphs": True,
        "full288_variable_KKT_root_not_claimed_isolated": True,
        "fresh_upper_report_sha256": sha(UPPER / "VERIFIED.json"), "fresh_local_report_sha256": sha(LOCAL),
        "old_entire_core_report_sha256": sha(CORE), "real_full_parent_transport_sha256": sha(TRANSPORT),
        "negative_same_root_upper_local_core_scope_controls_rejected": refused,
        "frozen_files": files, "source_sha256": sha(Path(__file__)),
        "all_four_lower_families_and_complete_global_content_freeze_still_required": True,
        "global_optimality_proved": False})
    print("N25 own exact R upper and fresh240 local minors with actual full core interface accepted;",
          "old whole-angle math honestly reused; final global proof still owed", flush=True)


if __name__ == "__main__":
    main()
