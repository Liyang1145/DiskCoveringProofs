"""Fresh strict trees only on a verified actual complete-type parent residual."""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
import argparse
import gzip
import json
import sys

from audit_n23_actual_full_type_stage import (
    ROOT, HIGH, read, publish, sha, no_duplicate_keys, check_bound_tree, exact)
from audit_n23_B15_effective_outer_payment import pending_indices

assert __debug__


def validate_row(row, before, after, unpaid):
    assert type(row["index"]) is int
    assert row["index"] == before["index"] == after["index"]
    assert row["outer_group"] == before["outer_group"] == after["outer_group"]
    if unpaid:
        assert before["status"] == "pending" and after["status"] in ("pending", "strict")
    elif before["status"] == "strict":
        assert after["status"] == "strict"
        assert after["tree_sha256"] == before["tree_sha256"]
        assert after["exact_result"] == before["exact_result"]
    else:
        assert before["status"] == "exact-candidate-full-type-retained"
        assert after == before


def main():
    ap = argparse.ArgumentParser()
    for name in ("restored", "parent", "stage", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    restored, parent, stage, controlpath, output = (
        getattr(args, name).resolve() for name in ("restored", "parent", "stage", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (restored, parent, stage, controlpath, output))
    assert not output.exists()
    accepted, source, summary, inputs, controls = map(read, (
        parent / "VERIFIED.json", restored / "VERIFIED.json", stage / "SUMMARY.json",
        stage / "INPUT-BINDINGS.json", controlpath))
    assert accepted["verified"] and accepted["schema"] in (
        "N23-original-complete-residual-type-fresh-force-core-payments-v1",
        "N23-iterative-complete-type-strict-supplement-payments-v1")
    assert accepted["source_sha256"] in (
        sha(ROOT / "audit_n23_actual_full_type_stage.py"), sha(Path(__file__)))
    assert (accepted["N"], accepted["B"]) == (23, 15)
    assert accepted["every_actual_current_residual_source_index_partitioned_once"]
    assert accepted["old_paid_source_types_reused_without_recounting_or_claim_of_new_old_tree_replay"]
    assert source["verified"] and source["actual_full_residual_types"] == 829
    assert source["source_sha256"] == sha(ROOT / "extract_n23_actual_residual_types.py")
    originaldigest = accepted.get("original_829_restoration_report_sha256",
                                 accepted.get("parent_residual_restoration_report_sha256"))
    assert originaldigest == sha(restored / "VERIFIED.json")
    assert controls["verified"] and controls["schema"] == "N23-complete-type-followup-selection-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n23_complete_type_followup.py")
    assert controls["audit_source_sha256"] == sha(Path(__file__))
    assert controls["frozen_full_tree_identity_checker_sha256"] == sha(ROOT / "audit_n23_actual_full_type_stage.py")
    assert summary["source_sha256"] == sha(ROOT / "refine_n23_complete_type_proposals.py")
    assert summary["input_bindings_sha256"] == sha(stage / "INPUT-BINDINGS.json")
    assert summary["outcomes_sha256"] == sha(stage / "OUTCOMES.jsonl")
    assert summary["actual_full_types_processed"] == 829
    assert inputs["previous_proposal_positive_types_not_reproposed"]
    assert inputs["previous_known_full_candidate_never_strictly_reproposed"]
    previous = Path(inputs["previous_stage_path"]).resolve()
    assert previous.is_relative_to(ROOT)
    assert sha(previous / "SUMMARY.json") == inputs["previous_stage_report_sha256"]
    fullpath = restored / source["full_types_file"]
    fullhash = sha(fullpath)
    assert fullpath.resolve().is_relative_to(restored)
    assert fullhash == source["full_types_sha256"] == inputs["restored_full_types_sha256"]
    assert sha(parent / "PENDING.jsonl") == accepted["pending_sha256"]
    assert sha(parent / "PAYMENTS.jsonl") == accepted["payments_sha256"]
    unpaid = set(pending_indices(parent / "PENDING.jsonl", 16790546))
    assert len(unpaid) == accepted["pending_full_types"] == summary["selected_prior_pending_full_types"] > 0
    oldpayments = {}
    with (parent / "PAYMENTS.jsonl").open(encoding="ascii") as stream:
        previousindex = -1
        for line in stream:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert type(row["index"]) is int and previousindex < row["index"]
            previousindex = row["index"]
            assert row["index"] not in unpaid
            oldpayments[row["index"]] = row
    assert len(oldpayments)+len(unpaid) == 829
    frozen = dict(accepted["frozen_files"])
    for path, digest in summary["frozen_files"].items():
        if path in frozen:
            assert frozen[path] == digest
        frozen[path] = digest
    assert frozen[str(previous / "SUMMARY.json")] == sha(previous / "SUMMARY.json")
    for path in (Path(__file__), parent / "VERIFIED.json", parent / "PENDING.jsonl",
                 parent / "PAYMENTS.jsonl", restored / "VERIFIED.json", fullpath,
                 previous / "SUMMARY.json", previous / "OUTCOMES.jsonl", controlpath,
                 stage / "SUMMARY.json", stage / "INPUT-BINDINGS.json", stage / "OUTCOMES.jsonl",
                 ROOT / "audit_n23_actual_full_type_stage.py"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    constantspath = HIGH.parent / "evidence/core-reduction/constants/n23.json"
    constants, constantshash = read(constantspath), sha(constantspath)
    assert constants["verified"] and constants["N"] == 23
    assert F(constants["radius_upper"]) == F(249953776586051, 10**15)
    counts, proposedcounts, newcounts = Counter(), Counter(), Counter()
    selected, allindices = set(), set()
    output.mkdir()
    with fullpath.open(encoding="ascii") as fulltypes, \
            (previous / "OUTCOMES.jsonl").open(encoding="ascii") as previousrows, \
            (stage / "OUTCOMES.jsonl").open(encoding="ascii") as outcomes, \
            (output / "PAYMENTS.jsonl").open("x", encoding="ascii") as payments, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as residual:
        for line in fulltypes:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            before = json.loads(next(previousrows), object_pairs_hook=no_duplicate_keys)
            after = json.loads(next(outcomes), object_pairs_hook=no_duplicate_keys)
            index = row["index"]
            assert index not in allindices
            allindices.add(index)
            validate_row(row, before, after, index in unpaid)
            proposedcounts[after["status"]] += 1
            if index in oldpayments:
                payment = oldpayments[index]
                if before["status"] == "strict":
                    assert payment["kind"] == "strict-complete-type-force"
                    assert payment["tree_sha256"] == before["tree_sha256"]
                    oldtree = (stage / after["certificate_path_relative_to_receipt"]).resolve()
                    assert oldtree.is_relative_to(ROOT)
                    assert frozen[str(oldtree)] == sha(oldtree) == payment["tree_sha256"]
                else:
                    assert payment["kind"] == "nonstrict-same-root-core"
                    assert payment["candidate_full_to_actual_map"] == before["candidate_full_to_actual_map"]
                payments.write(json.dumps(payment, separators=(",", ":"))+"\n")
                counts[payment["kind"]] += 1
                continue
            assert index in unpaid
            selected.add(index)
            newcounts[after["status"]] += 1
            if after["status"] == "pending":
                counts["pending"] += 1
                residual.write(json.dumps({"index": index})+"\n")
                continue
            treepath = stage / f"type-{index:08}.json.gz"
            assert sha(treepath) == after["tree_sha256"]
            with gzip.open(treepath, "rt", encoding="utf8") as stream:
                tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
            check_bound_tree(row, tree, fullhash, constantshash, constants)
            result = exact.verify(15, 23, row["faces"], tree["nodes"], constants)
            assert result == after["exact_result"] and F(result["minimum_force_margin"]) > 0
            frozen[str(treepath)] = sha(treepath)
            counts["strict-complete-type-force"] += 1
            payments.write(json.dumps({"index": index, "kind": "strict-complete-type-force",
                                       "tree_sha256": sha(treepath)}, separators=(",", ":"))+"\n")
            print("N23 actual pending full-type fresh strict supplement", len(selected),
                  "/", len(unpaid), flush=True)
        assert not previousrows.read(1) and not outcomes.read(1)
    assert selected == unpaid and allindices == set(oldpayments) | unpaid
    assert sum(counts.values()) == 829 and dict(proposedcounts) == summary["counts"]
    assert dict(newcounts) == summary["new_proposal_counts"]
    for path, digest in frozen.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath", "group_catalog"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-iterative-complete-type-strict-supplement-payments-v1",
        "N": 23, "B": 15, "original_catalog_types": 16790546,
        "original_restored_full_types": 829,
        "previous_pending_full_types": len(unpaid),
        "additional_strict_complete_types": newcounts["strict"],
        "counts": dict(counts), "pending_full_types": counts["pending"],
        "every_actual_current_residual_source_index_partitioned_once": True,
        "all_new_strict_type_trees_independently_replayed_on_all_29_actual_faces": True,
        "old_paid_source_types_reused_without_recounting_or_claim_of_new_old_tree_replay": True,
        "previous_attaining_core_payment_preserved_nonstrict_not_recast_as_strict": True,
        "full_source_and_maps_previously_scanned_in_bound_restoration": True,
        "parent_report_sha256": sha(parent / "VERIFIED.json"),
        "original_829_restoration_report_sha256": sha(restored / "VERIFIED.json"),
        "payments_sha256": sha(output / "PAYMENTS.jsonl"),
        "pending_sha256": sha(output / "PENDING.jsonl"),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "other_boundary_families_and_global_cover_synthesis_still_required": True,
        "global_optimality_proved": False,
    })
    print("N23 actual full-type strict supplement accepted:", dict(counts), flush=True)


if __name__ == "__main__":
    main()
