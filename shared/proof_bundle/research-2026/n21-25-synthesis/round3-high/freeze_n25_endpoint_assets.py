"""Freeze precisely the paid endpoint-core theorems, NEVER global n25 optimum."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import sys
import n25_anchor_isolation as field
import exact_graph as exact
from replay_n25_endpoint_domain import inputs
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[2].resolve()
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    constants, masks, _, bindings, negative = inputs(-1)
    U = F(constants["radius_upper"])
    assert (field.Q.Q2(U*U)-field.Q.Q2(1, -F(2, 3))).sign() > 0
    sys.path.insert(0, str(exact.kernel.ARCS))
    import exact_arcs as arcs
    for k, cap in enumerate(constants["angle_caps"], 1):
        assert F(arcs.sincos_turn(F(cap, 2*constants["angle_scale"]))[1][0], arcs.SCALE) > k*U
    replaypath = ROOT / "evidence/n25-endpoint-negative-angle-complete-independent-resume1.json"
    replay = read(replaypath)
    treepath = ROOT / "evidence/n25-endpoint-negative-angle-prefix600001-resume1/endpoint-angle-tree.json.gz"
    assert replay["verified"] and replay["entire_angle_domain_proved"] and replay["pending_boxes"] == 0
    assert replay["nodes"] == 426937 and replay["input_sha256"] == bindings
    assert replay["source_sha256"] == sha(ROOT / "replay_n25_endpoint_domain.py")
    assert replay["tree_sha256"] == sha(treepath)
    assert F(replay["minimum_force_margin"]) > 0 and F(replay["minimum_local_margin"]) > 0
    transferpath = ROOT / "evidence/n25-both-endpoint-whole-angle-transfer-resume1.json"
    transfer = read(transferpath)
    assert transfer["verified"] and transfer["both_endpoint_core_lower_bounds"]
    assert transfer["negative_replay_sha256"] == sha(replaypath)
    assert transfer["negative_tree_sha256"] == sha(treepath) and transfer["input_sha256"] == bindings
    assert transfer["source_sha256"] == sha(ROOT / "n25_endpoint_angle_transfer.py")
    assert len(transfer["negative_controls_rejected"]) == 3
    completionpath = ROOT / "evidence/n25-endpoint-completion-unique-resume1.json"
    completion = read(completionpath)
    assert completion["verified"] and completion["both_sparse_rod_cores_keep_full_center_skeleton"]
    assert completion["same_order_topology_completion_family_not_enlarged"]
    assert completion["source_sha256"] == sha(ROOT / "n25_endpoint_completion.py")
    assert completion["endpoint_report_sha256"] == bindings["local"]
    assert completion["geometry_sha256"] == bindings["geometry"]
    tightpath = ROOT / "evidence/n25-endpoint-tight-isolation-gamma2000-resume1/REPORT.json"
    repeatpath = ROOT / "evidence/n25-endpoint-tight-isolation-gamma2000-replay-resume1/REPORT.json"
    tight = read(tightpath)
    assert tight["verified"] and tightpath.read_bytes() == repeatpath.read_bytes()
    assert tight["source_sha256"] == sha(ROOT / "n25_endpoint_tight_isolation.py")
    assert tight["geometry_sha256"] == bindings["geometry"] and tight["fibre_report_sha256"] == bindings["fibre"]
    assert tight["stress_character_sha256"] == bindings["character"]
    assert all(row["verified"] and row["positive_leading_principal_minors"] == 120 and
               row["gamma"] == 2000 and F(row["lambda"]) == F(1, 5000) and
               F(row["nu"]) == F(21, 5000) and F(row["anchor_radius"]) == F(1, 20) and
               F(row["isolation_margin"]) == F(59, 2500000) for row in tight["cores"])
    kktpath = ROOT / "evidence/n25-reduced-kkt-resume1.json"
    kktrepeat = ROOT / "evidence/n25-reduced-kkt-replay-resume1.json"
    kkt = read(kktpath)
    assert kkt["verified"] and kktpath.read_bytes() == kktrepeat.read_bytes()
    assert kkt["source_sha256"] == sha(ROOT / "n25_reduced_kkt.py")
    assert kkt["nonsingularity_written_argument_sha256"] == sha(ROOT / "N25-STRESS-ENDPOINT-CORES.md")
    assert kkt["geometry_sha256"] == bindings["geometry"]
    assert kkt["isolation_report_sha256"] == kkt["isolation_replay_sha256"] == bindings["local"]
    assert kkt["affine_fibre_report_sha256"] == bindings["fibre"]
    assert kkt["stress_character_sha256"] == bindings["character"]
    assert not kkt["full_288_variable_KKT_root_isolated"]
    assert sorted(row["parameter_sign"] for row in kkt["reduced_cores"]) == [-1, 1]
    assert all(row["dimension"] == 228 and row["G"] == 120 and row["M"] == 92 and
               row["all_quadratic_root_equations_rechecked"] and
               row["normalized_reduced_stress_unique_by_extension"] and
               row["square_KKT_Jacobian_nonsingularity_block_prerequisites_verified"]
               for row in kkt["reduced_cores"])
    files = [
        Path(__file__), ROOT / "N25-STRESS-ENDPOINT-CORES.md",
        ROOT / "N25-STRESS-ENDPOINT-CORES-ADVANCE.md", replaypath, treepath, transferpath,
        completionpath, tightpath, repeatpath, kktpath, kktrepeat,
        ROOT / "evidence/n25-endpoint-core-isolation-resume1/REPORT.json",
        ROOT / "evidence/n25-endpoint-core-isolation-replay-resume1/REPORT.json",
        ROOT / "evidence/n25-isolation-exact-resume1/rotated-geometry.json",
        ROOT / "evidence/n25-isolation-exact-resume1/VERIFIED.json",
        ROOT / "evidence/n25-stress-freedom-exact-resume1/VERIFIED.json",
        ROOT / "evidence/n25-stress-character-resume2.json",
        ROOT / "evidence/n25-stress-character-replay-resume2.json",
        ROOT / "evidence/n25-endpoint-partition-controls-resume1.json",
        ROOT / "test_n25_endpoint_partition.py",
        ROOT / "n25_endpoint_angle_transfer.py", ROOT / "n25_endpoint_completion.py",
        ROOT / "replay_n25_endpoint_domain.py", ROOT / "n25_endpoint_domain.py",
        ROOT / "n25_endpoint_core_isolation.py", ROOT / "n25_endpoint_tight_isolation.py",
        ROOT / "n25_anchor_isolation.py", ROOT / "n25_stress_character.py",
        ROOT / "n25_stress_freedom.py", ROOT / "n25_reduced_kkt.py",
        ROOT / "replay_candidate.py", ROOT / "exact_graph.py", ROOT / "stream_catalog.py",
        ROOT / "audit_snapshot_files.py", ROOT.parent / "n25_algebraic_upper.py",
        ROOT.parent / "n25_core_analysis.py", ROOT.parent / "round2-grouped/partial_force_exact.py",
        ROOT.parent / "evidence/core-reduction/constants/n25.json",
        ROOT.parent / "evidence/n25-algebraic-upper-round2/geometry.json",
        ROOT.parent / "evidence/n25-algebraic-upper-round2/VERIFIED.json",
        ROOT.parent / "evidence/n25-core-analysis-stable3/stress-verified.json",
        exact.kernel.ARCS / "exact_arcs.py",
    ]
    digests = {}
    for path in files:
        resolved = path.resolve()
        assert resolved.is_relative_to(WORK)
        digests[resolved.relative_to(WORK).as_posix()] = sha(resolved)
    report = {"verified": True, "N": 25, "schema": "n25-two-endpoint-core-lower-assets-v1",
              "both_61_node_92_rod_whole_angle_lower_bounds_paid": True,
              "two_228_variable_roots_locally_unique": True,
              "original_288_variable_root_is_not_isolated": True,
              "larger_1_over_20_anchor_isolation_replayed_twice": True,
              "same_n_B16_full_completion_unique_not_expanded": True,
              "whole_unit_disk_upper_not_paid_by_this_snapshot": True,
              "all_competing_topologies_not_paid_by_this_snapshot": True,
              "global_optimality_proved": False, "formalization_completed": False,
              "source_sha256": sha(Path(__file__)), "file_count": len(digests), "files": digests,
              "scope": "specified two endpoint-core theorems and exact completion lemma only"}
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N25 endpoint assets SNAPSHOT PASS:", len(digests),
          "files; explicitly NOT an unrestricted n25 proof", flush=True)


if __name__ == "__main__":
    main()
