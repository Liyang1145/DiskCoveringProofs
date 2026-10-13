"""Independent exact replay and disjoint payment of restored complete N23 types."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from audit_streamed_hierarchy import check_map
from audit_n23_B15_effective_outer_payment import pending_indices
import exact_graph as exact

assert __debug__


def check_bound_tree(row, tree, fullhash, constantshash, constants):
    assert (tree["N"], tree["B"], tree["full_centers"]) == (23, 15, 23)
    assert type(tree["index"]) is int and tree["index"] == row["index"]
    assert tree["faces"] == row["faces"] and len(tree["faces"]) == 29
    assert tree["restored_full_types_sha256"] == fullhash
    assert tree["constants_sha256"] == constantshash
    assert tree["radius_upper"] == constants["radius_upper"]
    assert tree["nodes"] and all(node["kind"] in ("EMPTY", "SPLIT", "DUAL")
                                 for node in tree["nodes"])


def check_complete_candidate(row, mapping, candidate):
    assert len(row["faces"]) == len(candidate) == 29
    check_map(23, 15, {"centers": 23, "faces": candidate},
              mapping, set(row["faces"]), 0)


def main():
    ap = argparse.ArgumentParser()
    for name in ("restored", "stage", "core", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--core-proof", type=Path)
    args = ap.parse_args()
    restored, stage, corepath, controlpath, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("restored", "stage", "core", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (restored, stage, corepath, controlpath, output))
    assert not output.exists()
    accepted, summary, inputs, controls, core = map(read, (
        restored / "VERIFIED.json", stage / "SUMMARY.json",
        stage / "INPUT-BINDINGS.json", controlpath, corepath))
    assert accepted["verified"]
    assert accepted["schema"] == "original-N23-B15-actual-complete-residual-types-restoration-v1"
    assert accepted["source_sha256"] == sha(ROOT / "extract_n23_actual_residual_types.py")
    assert accepted["only_current_parent_pending_indices_selected"]
    assert accepted["all_original_source_rows_and_bindings_scanned_to_real_end"]
    assert controls["verified"]
    assert controls["schema"] == "N23-actual-full-type-tree-and-candidate-identity-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n23_actual_full_type_stage.py")
    assert controls["audit_source_sha256"] == sha(Path(__file__))
    assert summary["source_sha256"] == sha(ROOT / "propose_n23_actual_full_types.py")
    assert summary["input_bindings_sha256"] == sha(stage / "INPUT-BINDINGS.json")
    assert summary["outcomes_sha256"] == sha(stage / "OUTCOMES.jsonl")
    assert summary["actual_full_types_processed"] == accepted["actual_full_residual_types"]
    assert inputs["restoration_report_sha256"] == sha(restored / "VERIFIED.json")
    assert (core["N"], core["B"]) == (23, 15)
    candidate = sorted(sum(1 << v for v in face) for face in core["all_faces"])
    assert inputs["candidate_full_faces"] == candidate
    fullpath = restored / accepted["full_types_file"]
    fullhash = sha(fullpath)
    assert fullpath.resolve().is_relative_to(restored)
    assert fullhash == accepted["full_types_sha256"] == inputs["restored_full_types_sha256"]
    constantspath = HIGH.parent / "evidence/core-reduction/constants/n23.json"
    constants = read(constantspath)
    constantshash = sha(constantspath)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    frozen = dict(accepted["frozen_files"])
    for path, digest in summary["frozen_files"].items():
        if path in frozen:
            assert frozen[path] == digest
        frozen[path] = digest
    coreproof = None
    if args.core_proof is not None:
        coreproofpath = args.core_proof.resolve()
        assert coreproofpath.is_relative_to(ROOT)
        coreproof = read(coreproofpath)
        assert coreproof["verified"]
        assert coreproof["schema"] == "isolated-N23-same-root-upper-local-and-entire-core-domain-replay-v1"
        assert coreproof["source_sha256"] == sha(ROOT / "replay_isolated_n23_core_prerequisites.py")
        assert (coreproof["N"], coreproof["B"], coreproof["core_centers"]) == (23, 15, 23)
        assert coreproof["system_sha256"] == sha(corepath)
        assert coreproof["constants_sha256"] == constantshash
        assert coreproof["whole_core_lower_bound_is_nonstrict_same_root_not_strict_upper_exclusion"]
        assert coreproof["root_interval_certificate_freshly_recomputed"]
        assert coreproof["all_local_exact_principal_minors_and_perturbation_gap_recomputed"]
        assert coreproof["all_30653_core_angle_nodes_freshly_replayed"]
        expectedmasks = sorted(sum(1 << v for v in face) for face in core["active_faces"])
        assert core["center_core_nodes"] == list(range(15, 38))
        assert coreproof["core_faces"] == expectedmasks and set(expectedmasks) <= set(candidate)
        # Independently identify the exact anchor/face rod graph to which the
        # root and local isolation apply, including witness reindexing.
        assert core["edges"][:30] == (
            [[i, 15+i] for i in range(15)]
            + [[i, 15+(i+1) % 15] for i in range(15)])
        for j, face in enumerate(core["active_faces"]):
            assert core["edges"][30+3*j:30+3*j+3] == [[38+j, 15+v] for v in face]
        assert len(core["edges"]) == 30+3*len(core["active_faces"])
        for name, key in (
            ("root-verified.json", "fresh_root_report_sha256"),
            ("upper-verified.json", "fresh_upper_report_sha256"),
            ("FRESH-LOCAL-ISOLATION.json", "fresh_local_report_sha256"),
            ("FRESH-ANGLE-REPLAY.json", "fresh_angle_report_sha256"),
        ):
            path = coreproofpath.parent / name
            assert sha(path) == coreproof[key]
            frozen[str(path)] = sha(path)
        for path, digest in coreproof["frozen_files"].items():
            if path in frozen:
                assert frozen[path] == digest
            frozen[path] = digest
        frozen[str(coreproofpath)] = sha(coreproofpath)
    for path in (Path(__file__), restored / "VERIFIED.json", stage / "SUMMARY.json",
                 stage / "INPUT-BINDINGS.json", stage / "OUTCOMES.jsonl", fullpath,
                 corepath, constantspath, controlpath,
                 ROOT / "test_n23_actual_full_type_stage.py",
                 HIGH / "exact_graph.py", HIGH / "audit_streamed_hierarchy.py",
                 Path(exact.kernel.__file__)):
        frozen[str(path.resolve())] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    pendingpaths = [Path(path) for path, digest in accepted["frozen_files"].items()
                    if Path(path).name == "PENDING.jsonl" and digest == accepted["pending_sha256"]]
    assert len(pendingpaths) == 1
    pending = pending_indices(pendingpaths[0], 16790546)
    counts, groups, proposed_counts = Counter(), Counter(), Counter()
    output.mkdir()
    with fullpath.open(encoding="ascii") as fulltypes, \
            (stage / "OUTCOMES.jsonl").open(encoding="ascii") as outcomes, \
            (output / "PAYMENTS.jsonl").open("x", encoding="ascii") as payments, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as residual:
        for full_line in fulltypes:
            row = json.loads(full_line, object_pairs_hook=no_duplicate_keys)
            line = outcomes.readline()
            assert line
            outcome = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert outcome["index"] == row["index"] == next(pending)
            assert outcome["outer_group"] == row["outer_group"]
            proposed_counts[outcome["status"]] += 1
            groups[str(row["outer_group"])] += 1
            if outcome["status"] == "strict":
                treepath = stage / f"type-{row['index']:08}.json.gz"
                assert sha(treepath) == outcome["tree_sha256"]
                with gzip.open(treepath, "rt", encoding="utf8") as source:
                    tree = json.load(source, object_pairs_hook=no_duplicate_keys)
                check_bound_tree(row, tree, fullhash, constantshash, constants)
                result = exact.verify(15, 23, row["faces"], tree["nodes"], constants)
                assert result == outcome["exact_result"]
                assert result["verified"] and F(result["minimum_force_margin"]) > 0
                frozen[str(treepath)] = sha(treepath)
                payments.write(json.dumps({
                    "index": row["index"], "kind": "strict-complete-type-force",
                    "tree_sha256": sha(treepath)}, separators=(",", ":"))+"\n")
                counts["strict-complete-type-force"] += 1
            elif outcome["status"] == "exact-candidate-full-type-retained":
                mapping = outcome["candidate_full_to_actual_map"]
                check_complete_candidate(row, mapping, candidate)
                if coreproof is None:
                    counts["pending"] += 1
                    residual.write(json.dumps({"index": row["index"]})+"\n")
                else:
                    payments.write(json.dumps({
                        "index": row["index"], "kind": "nonstrict-same-root-core",
                        "candidate_full_to_actual_map": mapping,
                        "core_proof_sha256": sha(coreproofpath)}, separators=(",", ":"))+"\n")
                    counts["nonstrict-same-root-core"] += 1
            else:
                assert outcome["status"] == "pending"
                counts["pending"] += 1
                residual.write(json.dumps({"index": row["index"]})+"\n")
            if sum(counts.values()) % 50 == 0:
                print("N23 actual full-type independent exact payments", sum(counts.values()),
                      "/", accepted["actual_full_residual_types"], dict(counts), flush=True)
        assert not outcomes.read(1)
        assert next(pending, None) is None
    assert sum(counts.values()) == accepted["actual_full_residual_types"]
    assert dict(groups) == accepted["selected_original_outer_group_members"]
    assert dict(proposed_counts) == summary["counts"]
    for path, digest in frozen.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath", "group_catalog"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-original-complete-residual-type-fresh-force-core-payments-v1",
        "N": 23, "B": 15, "original_catalog_types": 16790546,
        "previous_pending_full_types": accepted["actual_full_residual_types"],
        "counts": dict(counts), "pending_full_types": counts["pending"],
        "every_actual_current_residual_source_index_partitioned_once": True,
        "all_29_faces_in_every_strict_full_type_tree_independently_bound_and_replayed": True,
        "nonstrict_core_requires_complete_actual_type_map_and_fresh_core_prerequisites": True,
        "outer_group_identity_alone_never_pays_all_group_members": True,
        "old_paid_source_types_reused_without_recounting_or_claim_of_new_old_tree_replay": True,
        "full_source_and_outer_maps_scanned_in_bound_restoration_not_repeated_in_this_layer": True,
        "parent_residual_restoration_report_sha256": sha(restored / "VERIFIED.json"),
        "payments_sha256": sha(output / "PAYMENTS.jsonl"),
        "pending_sha256": sha(output / "PENDING.jsonl"),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "other_boundary_families_and_global_cover_synthesis_still_required": True,
        "global_optimality_proved": False,
    })
    print("N23 actual full residual exact payment accepted:", dict(counts), flush=True)


if __name__ == "__main__":
    main()
