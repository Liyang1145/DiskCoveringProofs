"""Actual current28 mathematical transfer controls, NOT a geometry acceptance."""

from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_closed_ear_cover_transfer as transfer
import verify_conditional_force_stage as binding
from audit_prefix_partition import linux


def main():
    output = Path("outputs/n26-current28-closed-ear-original-owner-shadow-transfer-controls-v1.json")
    if output.exists():
        raise FileExistsError(output)
    current_path = Path("outputs/n26-twenty-eighth-conditional-current-audit-v28-sparse-v1-strict-with-owned8-scope.json")
    final_path = Path("outputs/n26-twenty-eighth-conditional-final-digest-recheck-v28-sparse-v1-strict-with-owned8.json")
    source_path = Path("outputs/n26-conditional-force-stage-v28-sparse-v1/FRONTIER.json")
    constants_path = Path("outputs/n26-new-scope-v1/CONSTANTS.json")
    certificate_paths = {
        "cap": Path("outputs/n26-universal-unit-cap-polynomial-certificate-v1.json"),
        "generic": Path("outputs/n26-universal-strict-slack-generic-position-polynomial-certificate-v1.json"),
        "bridge": Path("outputs/n26-empty-circle-corner-starring-universal-algebra-v1.json"),
    }
    proof_paths = {key: Path("work")/name for key, name in {
        "cap": "n26-unit-cap-domination-and-no-return-proof.md",
        "generic": "n26-strict-slack-generic-position-proof.md",
        "bridge": "n26-embedded-dual-and-corner-starring-bridge-proof.md",
        "ear": "n26-closed-ear-core-capacity-proof.md",
    }.items()}
    paths = [current_path, final_path, source_path, constants_path, Path(__file__), Path(transfer.__file__),
             *certificate_paths.values(), *proof_paths.values(),
             Path("outputs/n26-empty-circle-corner-starring-independent-controls-v1.json"),
             Path("work/audit_n26_closed_ear_core_capacity.py"),
             Path("work/test_n26_closed_ear_core_capacity.py"),
             Path(transfer.force.__file__), Path(transfer.bridge.__file__),
             Path(transfer.cap.__file__), Path(transfer.generic.__file__)]
    digests = {str(path): binding.sha(path) for path in paths}
    parent, final = binding.read(current_path), binding.read(final_path)
    if (final["current_audit_sha256"] != digests[str(current_path)]
            or parent["files"][linux(source_path)] != digests[str(source_path)]
            or final["Rstar_conditional_frontier_pending_subtrees"] != 11183
            or final["candidate_angle_unresolved_closed_boxes"] != 25):
        raise ValueError("mathematical transfer changed the actual completed current28 pair/source")
    source, constants = binding.read(source_path), binding.read(constants_path)
    certificates = {key: binding.read(path) for key, path in certificate_paths.items()}
    proofs = {key: binding.sha(path) for key, path in proof_paths.items()}
    frontier, ledger, result = transfer.partition(source, constants, certificates, proofs)
    if (result["closed_ear_whole_prefixes"] != 643
            or result["closed_ear_boundary_family_counts"] != {"16": 3, "17": 640}
            or len(frontier["pending_states"]) != 10540
            or result["original_physical_count_cases_checked"] != 646
            or result["original_physical_count_AND_all_shadow_label_placement_cases_checked"] != 673):
        raise AssertionError("actual current transfer/case conservation differs")
    negative = []
    def reject(name, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negative.append(name)
        else:
            raise AssertionError("unsafe ear transfer premise accepted: "+name)
    for name, field, value in (
        ("B17-under26-original-disks-hidden-by-padding", "minimum_interior_cells", 8),
        ("original-owner-count-dropped", "maximum_boundary_cells", 18),
        ("external-eight-disk-theorem-assumption-hidden", "external_n8_theorem_assumed", False),
        ("radius-screen-changed", "radius_upper", "1/4"),
    ):
        changed = deepcopy(constants)
        changed[field] = value
        reject(name, lambda changed=changed: transfer.original_count_cases(17, changed))
    changed = deepcopy(source)
    changed["inherited_source_is_unconditional_at_U"] = True
    reject("inherited-conditional-source-promoted-to-original-U",
           lambda: transfer.partition(changed, constants, certificates, proofs))
    changed_certificates = deepcopy(certificates)
    changed_certificates["bridge"]["explicit_ordered_real_hypotheses"].pop()
    reject("shadow-nearest-diagram-substituted-for-original-owner-frame",
           lambda: transfer.lemma_gate(changed_certificates, proofs))
    changed_proofs = dict(proofs)
    changed_proofs.pop("ear")
    reject("continuous-closed-ear-argument-not-bound",
           lambda: transfer.lemma_gate(certificates, changed_proofs))
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("actual mathematical transfer inputs changed")
    report = {
        "schema": "N26-current28-original-owner-shadow-ear-mathematical-transfer-controls-v1",
        "verified": False, "input_sha256": digests,
        "actual_source_mathematical_result": result,
        "all_original_m_and_shadow_label_placement_cases_for_643actual_prefixes_checked": True,
        "B17_actual_original_count_case": [26],
        "B16_actual_original_count_cases": [25, 26],
        "prospective_filtered_frontier_count_NOT_current": len(frontier["pending_states"]),
        "prospective_filtered_family_counts_NOT_current": frontier["families"],
        "actual_invalid_count_owner_scope_and_continuous_proof_controls_rejected": negative,
        "actual_full_source_history_geometry_dependency_replay_NOT_performed": True,
        "not_an_actual_geometry_acceptance_or_current_adoption": True,
        "all_existing_current_sources_proof_receipts_histories_and_ledgers_UNMODIFIED": True,
        "actual_current_transport_frontier_STILL": 11183,
        "actual_current_whole_candidate_roots_STILL": 25,
        "new_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "frozen_geometric_reduction_proved": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "entire_actual_source_prefixes_reconstructed": result["entire_actual_source_prefixes_reconstructed"],
        "actual_prefixes_with_complete_original_and_shadow_case_cover": len(ledger),
        "original_m_and_shadow_placement_cases": result["original_physical_count_AND_all_shadow_label_placement_cases_checked"],
        "prospective_frontier_NOT_current": len(frontier["pending_states"]),
        "actual_geometry_admission": False, "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
