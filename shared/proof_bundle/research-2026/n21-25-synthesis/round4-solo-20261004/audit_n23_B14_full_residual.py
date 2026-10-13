"""Exact full-type strict payments on the genuine accepted B14 residual."""
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
from audit_n23_B14_pending_outer import IndexedOriginal
from audit_n23_B15_effective_outer_payment import pending_indices
import exact_graph as exact

assert __debug__


def parent_gate(parent, sourcepath):
    accepted, source = read(parent / "VERIFIED.json"), read(sourcepath)
    assert accepted["verified"]
    assert accepted["schema"] == "N23-B14-current-pending-full-outer-strict-increment-v1"
    assert accepted["source_sha256"] == sha(ROOT / "audit_n23_B14_pending_outer.py")
    assert (accepted["N"], accepted["B"], accepted["original_catalog_types"]) == (23, 14, 8277632)
    assert accepted["every_previous_pending_source_index_partitioned_exactly_once"]
    assert accepted["every_current_pending_actual_complete_source_row_and_full_exposed_map_checked"]
    assert accepted["every_new_positive_force_tree_freshly_mathematically_replayed"]
    assert accepted["pending_full_types"] > 0
    assert accepted["frozen_files"][str(sourcepath)] == sha(sourcepath)
    assert source["verified"]
    assert source["schema"] == "restored-N23-B14-historical-complete-source-and-fresh-union-gates-v1"
    assert source["source_sha256"] == sha(ROOT / "accept_n23_B14_restored_source.py")
    catalogpath = (ROOT / source["catalog_relative_to_round4"]).resolve()
    assert catalogpath.is_relative_to(ROOT) and sha(catalogpath) == source["catalog_sha256"]
    assert accepted["frozen_files"][str(catalogpath)] == sha(catalogpath)
    assert sha(parent / "PENDING.jsonl") == accepted["pending_sha256"]
    assert sha(parent / "ADDITIONAL-PAYMENTS.jsonl") == accepted["additional_payments_sha256"]
    frozen = dict(accepted["frozen_files"])
    for path in (sourcepath, catalogpath, parent / "VERIFIED.json", parent / "PENDING.jsonl",
                 parent / "ADDITIONAL-PAYMENTS.jsonl"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    return accepted, catalogpath, frozen


def check_tree(index, original, tree, pendinghash, constantshash, constants):
    assert type(index) is int and type(tree["index"]) is int and tree["index"] == index
    assert (tree["N"], tree["B"], tree["full_centers"]) == (23, 14, 23)
    faces = original["faces"]
    assert len(faces) == 30 and faces == sorted(set(faces))
    assert tree["faces"] == faces
    assert tree["parent_pending_sha256"] == pendinghash
    assert tree["constants_sha256"] == constantshash
    assert tree["radius_upper"] == constants["radius_upper"]
    assert tree["nodes"] and all(node["kind"] in ("EMPTY", "SPLIT", "DUAL")
                                 for node in tree["nodes"])
    result = exact.verify(14, 23, faces, tree["nodes"], constants)
    assert result["verified"] and F(result["minimum_force_margin"]) > 0
    return result


def outcomes_for_pending(pending, outcomes, expected):
    seen = 0
    for index in pending:
        line = outcomes.readline()
        assert line, "missing actual complete-type outcome"
        outcome = json.loads(line, object_pairs_hook=no_duplicate_keys)
        assert type(outcome["index"]) is int and outcome["index"] == index
        assert outcome["status"] in ("strict", "pending")
        seen += 1
        yield index, outcome
    assert seen == expected and not outcomes.read(1)


def main():
    ap = argparse.ArgumentParser()
    for name in ("source", "parent", "stage", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    sourcepath, parent, stage, controlpath, output = (
        getattr(args, name).resolve() for name in ("source", "parent", "stage", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (sourcepath, parent, stage, controlpath, output))
    assert not output.exists()
    accepted, catalogpath, frozen = parent_gate(parent, sourcepath)
    receipt, controls = read(stage / "SUMMARY.json"), read(controlpath)
    assert controls["verified"] and controls["schema"] == "N23-B14-actual-full-residual-type-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n23_B14_full_residual.py")
    assert controls["audit_source_sha256"] == sha(Path(__file__))
    assert controls["proposal_source_sha256"] == sha(ROOT / "propose_n23_B14_full_residual.py")
    assert receipt["source_sha256"] == sha(ROOT / "propose_n23_B14_full_residual.py")
    assert receipt["parent_report_sha256"] == sha(parent / "VERIFIED.json")
    assert receipt["parent_pending_sha256"] == accepted["pending_sha256"]
    assert receipt["actual_full_types_processed"] == accepted["pending_full_types"]
    assert receipt["all_actual_complete_faces_retained_not_outer_only"]
    assert (receipt["N"], receipt["B"]) == (23, 14)
    outcomespath = stage / "OUTCOMES.jsonl"
    assert sha(outcomespath) == receipt["outcomes_sha256"]
    assert sha(stage / "INPUT-BINDINGS.json") == receipt["input_bindings_sha256"]
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    constants, constantshash = read(constants_path), sha(constants_path)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    for path, digest in receipt["frozen_files"].items():
        assert path not in frozen or frozen[path] == digest
        frozen[path] = digest
    for path in (Path(__file__), controlpath, stage / "SUMMARY.json", stage / "INPUT-BINDINGS.json",
                 outcomespath, constants_path, ROOT / "audit_n23_B14_pending_outer.py",
                 HIGH / "exact_graph.py", Path(exact.kernel.__file__)):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    catalog = IndexedOriginal(catalogpath)
    output.mkdir()
    proposed, counts = Counter(), Counter()
    with outcomespath.open(encoding="ascii") as outcomes, \
            (output / "ADDITIONAL-PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as residual:
        joined = outcomes_for_pending(pending_indices(parent / "PENDING.jsonl", 8277632),
                                      outcomes, accepted["pending_full_types"])
        for index, outcome in joined:
            proposed[outcome["status"]] += 1
            original = catalog.at(index)
            if outcome["status"] == "pending":
                counts["pending"] += 1
                residual.write(json.dumps({"index": index}, separators=(",", ":"))+"\n")
            else:
                path = stage / f"type-{index:08}.json.gz"
                assert sha(path) == outcome["tree_sha256"]
                with gzip.open(path, "rt", encoding="utf8") as stream:
                    tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
                result = check_tree(index, original, tree, accepted["pending_sha256"],
                                    constantshash, constants)
                assert result == outcome["exact_result"]
                counts["strict-complete-type-force"] += 1
                frozen[str(path)] = sha(path)
                ledger.write(json.dumps({
                    "index": index, "kind": "strict-complete-type-force", "tree_sha256": sha(path),
                }, separators=(",", ":"))+"\n")
            if sum(counts.values()) % 500 == 0:
                print("N23/B14 actual complete-type independent payments", sum(counts.values()),
                      "/", accepted["pending_full_types"], dict(counts), flush=True)
    catalog.close()
    assert sum(counts.values()) == accepted["pending_full_types"]
    assert dict(proposed) == receipt["counts"]
    for path, digest in frozen.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath", "group_catalog"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-B14-actual-full-residual-fresh-force-payment-v1",
        "N": 23, "B": 14, "original_catalog_types": 8277632,
        "previous_pending_full_types": accepted["pending_full_types"], "counts": dict(counts),
        "pending_full_types": counts["pending"],
        "every_genuine_previous_pending_source_index_partitioned_once": True,
        "every_positive_full23center30face_type_freshly_mathematically_replayed": True,
        "pure_internal_faces_never_dropped_or_substituted_by_outer_group_identity": True,
        "previous_source_and_old_tree_proofs_bound_prerequisites_not_new_old_math_replays": True,
        "not_a_fresh_complete_original_catalog_scan": True,
        "parent_report_sha256": sha(parent / "VERIFIED.json"),
        "additional_payments_sha256": sha(output / "ADDITIONAL-PAYMENTS.jsonl"),
        "pending_sha256": sha(output / "PENDING.jsonl"), "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)),
        "source_completeness_actual_cover_transport_and_global_assembly_still_owed": True,
        "global_optimality_proved": False,
    })
    print("N23/B14 actual full residual strict payments accepted:", dict(counts), flush=True)


if __name__ == "__main__":
    main()
