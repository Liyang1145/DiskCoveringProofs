"""Independent whole-type supplement replay; optional actual-parent adoption.

The discovery subset is not itself a formal previous residual. Optional
adoption requires the independently accepted full1 parent and its exact
current pending indices, never a proposal's pending count alone.
"""
from pathlib import Path
from collections import Counter
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from audit_n23_B14_full_residual import parent_gate, check_tree, outcomes_for_pending
from audit_n23_B14_pending_outer import IndexedOriginal
from audit_n23_B15_effective_outer_payment import pending_indices

assert __debug__


def select_actual_proposal_pending(indices, outcomes, expected, expected_counts):
    counts, selected = Counter(), []
    for index, outcome in outcomes_for_pending(indices, outcomes, expected):
        counts[outcome["status"]] += 1
        if outcome["status"] == "pending":
            selected.append(index)
    assert dict(counts) == expected_counts
    assert selected == sorted(set(selected))
    return selected


def main():
    ap = argparse.ArgumentParser()
    for name in ("source", "original-parent", "previous-stage", "stage", "controls", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--accepted-parent", type=Path)
    args = ap.parse_args()
    sourcepath, original, previous, stage, controlpath, output = (
        getattr(args, name.replace("-", "_")).resolve()
        for name in ("source", "original-parent", "previous-stage", "stage", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (sourcepath, original, previous, stage, controlpath, output))
    assert not output.exists()
    accepted, catalogpath, frozen = parent_gate(original, sourcepath)
    old, summary, controls = read(previous / "SUMMARY.json"), read(stage / "SUMMARY.json"), read(controlpath)
    assert old["source_sha256"] == sha(ROOT / "propose_n23_B14_full_residual.py")
    assert old["parent_report_sha256"] == sha(original / "VERIFIED.json")
    assert old["parent_pending_sha256"] == accepted["pending_sha256"]
    assert old["outcomes_sha256"] == sha(previous / "OUTCOMES.jsonl")
    assert old["actual_full_types_processed"] == accepted["pending_full_types"]
    with (previous / "OUTCOMES.jsonl").open(encoding="ascii") as stream:
        selected = select_actual_proposal_pending(
            pending_indices(original / "PENDING.jsonl", 8277632), stream,
            accepted["pending_full_types"], old["counts"])
    assert selected and summary["selected_original_proposal_pending_indices"] == selected
    assert summary["source_sha256"] == sha(ROOT / "propose_n23_B14_selected_full_supplements.py")
    assert summary["previous_stage_report_sha256"] == sha(previous / "SUMMARY.json")
    assert summary["original_parent_report_sha256"] == sha(original / "VERIFIED.json")
    assert summary["parent_pending_sha256"] == accepted["pending_sha256"]
    assert summary["outcomes_sha256"] == sha(stage / "OUTCOMES.jsonl")
    assert controls["verified"] and controls["schema"] == "N23-B14-proposal-pending-full-supplement-selection-controls-v1"
    assert controls["source_sha256"] == sha(ROOT / "test_n23_B14_selected_full_supplements.py")
    assert controls["audit_source_sha256"] == sha(Path(__file__))
    assert controls["proposal_source_sha256"] == sha(ROOT / "propose_n23_B14_selected_full_supplements.py")
    assert controls["whole_type_math_checker_sha256"] == sha(ROOT / "audit_n23_B14_full_residual.py")
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    constants, constantshash = read(constants_path), sha(constants_path)
    for path, digest in summary["frozen_files"].items():
        assert path not in frozen or frozen[path] == digest
        frozen[path] = digest
    catalog = IndexedOriginal(catalogpath)
    paid, counts = {}, Counter()
    with (stage / "OUTCOMES.jsonl").open(encoding="ascii") as outcomes:
        for index, outcome in outcomes_for_pending(iter(selected), outcomes, len(selected)):
            counts[outcome["status"]] += 1
            if outcome["status"] == "pending":
                continue
            path = stage / f"type-{index:08}.json.gz"
            assert sha(path) == outcome["tree_sha256"]
            with gzip.open(path, "rt", encoding="utf8") as stream:
                tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
            result = check_tree(index, catalog.at(index), tree, accepted["pending_sha256"],
                                constantshash, constants)
            assert result == outcome["exact_result"]
            paid[index] = sha(path)
            frozen[str(path)] = sha(path)
    catalog.close()
    assert dict(counts) == summary["counts"]
    adopted = None
    if args.accepted_parent is not None:
        parent = args.accepted_parent.resolve()
        assert parent.is_relative_to(ROOT)
        base = read(parent / "VERIFIED.json")
        assert base["verified"] and base["schema"] == "N23-B14-actual-full-residual-fresh-force-payment-v1"
        assert base["source_sha256"] == sha(ROOT / "audit_n23_B14_full_residual.py")
        assert (base["N"], base["B"], base["original_catalog_types"]) == (23, 14, 8277632)
        assert base["every_genuine_previous_pending_source_index_partitioned_once"]
        assert base["every_positive_full23center30face_type_freshly_mathematically_replayed"]
        assert base["parent_report_sha256"] == sha(original / "VERIFIED.json")
        assert base["frozen_files"][str(previous / "SUMMARY.json")] == sha(previous / "SUMMARY.json")
        assert sha(parent / "PENDING.jsonl") == base["pending_sha256"]
        assert sha(parent / "ADDITIONAL-PAYMENTS.jsonl") == base["additional_payments_sha256"]
        actual = list(pending_indices(parent / "PENDING.jsonl", 8277632))
        assert actual == selected and len(actual) == base["pending_full_types"]
        for path, digest in base["frozen_files"].items():
            assert path not in frozen or frozen[path] == digest
            frozen[path] = digest
        for path in (parent / "VERIFIED.json", parent / "PENDING.jsonl", parent / "ADDITIONAL-PAYMENTS.jsonl"):
            frozen[str(path)] = sha(path)
        adopted = {"parent_report_sha256": sha(parent / "VERIFIED.json"),
                   "previous_pending_full_types": len(actual), "new_strict_types": len(paid),
                   "pending_full_types": len(actual)-len(paid)}
    for path in (Path(__file__), sourcepath, original / "VERIFIED.json",
                 previous / "SUMMARY.json", previous / "OUTCOMES.jsonl", stage / "SUMMARY.json",
                 stage / "OUTCOMES.jsonl", controlpath, constants_path,
                 ROOT / "audit_n23_B14_full_residual.py"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    output.mkdir()
    if adopted is not None:
        with (output / "ADDITIONAL-PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
                (output / "PENDING.jsonl").open("x", encoding="ascii") as pending:
            for index in selected:
                if index in paid:
                    ledger.write(json.dumps({
                        "index": index, "kind": "strict-complete-type-force", "tree_sha256": paid[index]},
                        separators=(",", ":"))+"\n")
                else:
                    pending.write(json.dumps({"index": index}, separators=(",", ":"))+"\n")
        adopted["additional_payments_sha256"] = sha(output / "ADDITIONAL-PAYMENTS.jsonl")
        adopted["pending_sha256"] = sha(output / "PENDING.jsonl")
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath", "group_catalog"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-B14-real-complete-type-strict-supplement-replay-and-optional-adoption-v1",
        "N": 23, "B": 14, "selected_original_proposal_pending_indices": selected,
        "all_new_positive_complete_type_trees_freshly_independently_replayed": True,
        "strict_complete_type_trees": len(paid), "proposal_pending_types": counts["pending"],
        "actual_parent_adoption": adopted,
        "proposal_subset_never_mistaken_for_a_formal_parent_residual": True,
        "old_parent_proofs_reused_unchanged_not_claimed_freshly_math_replayed": True,
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "source_completeness_actual_cover_transport_and_global_assembly_still_required": True,
        "global_optimality_proved": False,
    })
    print("N23/B14 actual complete-type supplements freshly replayed:", len(paid),
          "; formal actual parent adoption:", adopted, flush=True)


if __name__ == "__main__":
    main()
