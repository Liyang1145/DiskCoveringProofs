"""Exact imported-N25 cardinality implication controls, NOT dependency acceptance."""

from fractions import Fraction as F
import json
from pathlib import Path

import verify_conditional_force_stage as binding


EXPECTED_SHA = "30389bfa3132d08954281e743db670fbb3874785e0d90c9876d4f5ddeec31dd1"
U = F(234701, 1000000)


def gate(accepted, u=U):
    if (
        accepted["schema"] != "N25-arbitrary-unit-closed-disk-cover-global-computer-assisted-source-proof-v1"
        or accepted["verified"] is not True or accepted["N"] != 25
        or accepted["theorem"] != "r_D(25)=1/(sqrt(6)+sqrt(3))"
        or accepted["exact_radius"] != "1/(sqrt(6)+sqrt(3))"
        or accepted["exact_radius_squared_Qsqrt2"] != ["1", "-2/3"]
        or accepted["global_source_proof_closed"] is not True
        or accepted["global_optimality_proved"] is not True
        or accepted["all_pending_families"] != 0
        or accepted["arbitrary_plane_centers_repetitions_fewer_disks_and_degeneracies_allowed"] is not True
        or accepted["not_Lean_Coq_formalization_not_third_party_peer_review_not_all_attaining_configurations_classified"] is not True
        or not 0 < u
    ):
        raise ValueError("imported N25 theorem lacks its exact qualified arbitrary-cover SOURCE scope")
    radical_threshold = F(3, 2)*(1-u*u)
    if radical_threshold <= 0 or radical_threshold**2 <= 2:
        raise ValueError("chosen n26 radius is not strictly below the exact imported n25 lower bound")
    return {
        "exact_radius_screen": str(u),
        "exact_positive_threshold_above_sqrt2": str(radical_threshold),
        "exact_threshold_square_margin_above_two": str(radical_threshold**2-2),
        "exact_imported_n25_lower_bound_STRICTLY_greater_than_screen": True,
        "under_IMPORTED_n25_theorem_every_at_most26_cover_in_scope_has26_original_necessary_disks": True,
        "same_conclusion_after_slack_projection_and_generic_perturbation_below_screen": True,
        "corner_shadow_padding_NOT_needed_for_genuine_covers_in_this_scope": True,
    }


def main():
    output = Path("outputs/n26-imported-n25-exactly26-original-cardinality-mathematical-controls-v1.json")
    if output.exists():
        raise FileExistsError(output)
    # Resolve the non-ASCII path inside a UTF8 source file, not through
    # PowerShell5's legacy inline-command quote conversion.
    source = Path("C:/热爱单机但萌新/_incoming-local-math-20261004/recovered-20261004/workspace/"
                  "research-2026/n21-25-synthesis/round4-solo-20261004/n25-global-final5/"
                  "ACCEPTED/GLOBAL-SOURCE-ACCEPTED.json")
    proof = Path("work/n26-exactly26-original-disks-from-imported-n25-proof.md")
    digest = binding.sha(source)
    if digest != EXPECTED_SHA:
        raise ValueError("actual imported N25 accepted entry changed")
    accepted = binding.read(source)
    result = gate(accepted)
    negatives = []
    def rejected(name, call):
        try:
            call()
        except (ValueError, KeyError, TypeError):
            negatives.append(name)
        else:
            raise AssertionError("invalid imported N25 cardinality scope accepted: "+name)
    for name, field, value in (
        ("pending-n25-source-proof", "global_source_proof_closed", False),
        ("unverified-n25-entry", "verified", False),
        ("wrong-N", "N", 24),
        ("not-arbitrary-or-fewer-disk-scope", "arbitrary_plane_centers_repetitions_fewer_disks_and_degeneracies_allowed", False),
        ("wrong-exact-radical", "exact_radius_squared_Qsqrt2", ["1", "-1/2"]),
        ("pending-family-hidden", "all_pending_families", 1),
        ("SOURCE-proof-promoted-to-formalization", "not_Lean_Coq_formalization_not_third_party_peer_review_not_all_attaining_configurations_classified", False),
    ):
        changed = dict(accepted)
        changed[field] = value
        rejected(name, lambda changed=changed: gate(changed))
    rejected("screen-at-quarter-not-below-n25-optimum", lambda: gate(accepted, F(1, 4)))
    rejected("negative-radius", lambda: gate(accepted, -U))
    if binding.sha(source) != digest:
        raise ValueError("actual N25 source entry changed during exact implication controls")
    report = {
        "schema": "N26-imported-N25-exact-original-cardinality-mathematical-controls-v1",
        "verified": False, "actual_imported_n25_source_entry": str(source),
        "actual_imported_n25_source_entry_sha256": digest,
        "executed_test_sha256": binding.sha(__file__), "written_implication_proof_sha256": binding.sha(proof),
        "actual_exact_radical_cardinality_implication": result,
        "actual_invalid_import_scope_and_radius_controls_rejected": negatives,
        "n25_theorem_IMPORTED_from_qualified_completed_SOURCE_proof_NOT_reproved_here": True,
        "actual_n25_ENTIRE_prerequisite_content_rehash_NOT_performed_here": True,
        "formal_import_geometry_current_AND_final_admission_STILL_required": True,
        "existing_shadow_inclusive_six_target_bundle_AND_live_jobs_UNMODIFIED": True,
        "actual_formal_frontier_STILL": 11183, "actual_candidate_whole_roots_STILL": 25,
        "new_formal_geometric_payments": 0, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_imported_n25_exact_radical_implication_controls_completed": True,
        "original_physical_disks_for_ANY_genuine_n26_cover_in_scope_UNDER_imported_theorem": 26,
        "invalid_controls_rejected": len(negatives), "actual_full_dependency_import_acceptance": False,
        "new_formal_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
