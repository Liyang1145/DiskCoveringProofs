"""Actual SIX geometry DATA + NEW midarc body controls, NOT current admission."""

from copy import deepcopy
import json
from pathlib import Path

from audit_prefix_partition import linux
import n26_midarc_cover_transfer as transfer
import n26_midarc_source_accounting as accounting
import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-midarc-SIX-filtered-source-accounting-controls-v1.json")
    if output.exists():
        raise FileExistsError(output)
    six_folder = Path("outputs/n26-current28-six-target-source-geometry-v1")
    own_path = six_folder / "VERIFIED.json"
    publication_path = Path("outputs/n26-current28-six-target-source-geometry-published-replay-v1.json")
    accepted = binding.read(own_path)
    if (
        binding.read(publication_path) != accepted
        or binding.sha(publication_path) != binding.sha(own_path)
        or accepted["verified"] is not True
        or accepted["source_actual_current_frontier"] != 11183
        or accepted["geometry_accepted_filtered_frontier_REQUIRES_CURRENT_AND_FINAL"] != 5637
    ):
        raise ValueError("midarc controls require actual completed SIX geometry own/publication DATA")
    names = {
        "cap": "UNIT-CAP-CERTIFICATE.json", "generic": "GENERIC-CERTIFICATE.json",
        "bridge": "EMBEDDED-CORNER-CERTIFICATE.json",
    }
    proof_paths = {
        "cap": six_folder / "UNIT-CAP-PROOF.md",
        "generic": six_folder / "GENERIC-SLACK-PROOF.md",
        "bridge": six_folder / "EMBEDDED-CORNER-SHADOW-BRIDGE-PROOF.md",
        "ear": six_folder / "CLOSED-EAR-PROOF.md",
        "midarc": Path("work/n26-midarc-seven-and-six-target-filled-patch-proof.md"),
    }
    certificates = {key: binding.read(six_folder / name) for key, name in names.items()}
    proofs = {key: binding.sha(path) for key, path in proof_paths.items()}
    source_path = six_folder / "FRONTIER.json"
    constants_path = six_folder / "FAMILY-CONSTANTS.json"
    source, constants = binding.read(source_path), binding.read(constants_path)
    for name in ("FRONTIER.json", "FAMILY-CONSTANTS.json", *names.values(),
                 *(path.name for key, path in proof_paths.items() if key != "midarc")):
        if accepted["files"][name] != binding.sha(six_folder / name):
            raise ValueError("midarc control actual frozen SIX geometry DATA changed: " + name)
    producer_path = Path("outputs/n26-current28-midarc-filled-patches-mathematical-scan-v1.json")
    independent_path = Path("outputs/n26-current28-midarc-filled-patches-independent-controls-v1.json")
    producer, previous_controls = binding.read(producer_path), binding.read(independent_path)
    if (
        producer["verified"] is not False or previous_controls["verified"] is not False
        or producer["qualifying_whole_prefixes"] != 6226
        or previous_controls["independent_qualifying_whole_prefixes"] != 6226
        or previous_controls["independent_all_original_count_AND_shadow_label_cases_checked"] != 68088
        or previous_controls["additional_beyond_frozen_six_triangles_NOT_admitted"] != 680
    ):
        raise ValueError("midarc filtered-source controls lack actual entire11183-prefix mathematics")
    paths = [
        own_path, publication_path, source_path, constants_path,
        producer_path, independent_path, *proof_paths.values(),
        *(six_folder / name for name in names.values()),
        Path(__file__), Path(transfer.__file__), Path(accounting.__file__),
        Path(transfer.rule.__file__),
    ]
    digests = {linux(path): binding.sha(path) for path in paths}
    print("Freshly reconstructing all5637 SIX-filtered ORIGINAL prefixes and both label-set enumerations.",
          flush=True)
    frontier, ledger, semantic = transfer.partition(source, constants, certificates, proofs)
    result = accounting.partition_gate(source, frontier, ledger, constants, proofs)
    original_path = Path("outputs/n26-conditional-force-stage-v28-sparse-v1/FRONTIER.json")
    old_six_ledger_path = six_folder / "LOWER-LEDGER.json"
    original = binding.read(original_path)
    old_paid = binding.read(old_six_ledger_path)
    digests[linux(original_path)] = binding.sha(original_path)
    digests[linux(old_six_ledger_path)] = binding.sha(old_six_ledger_path)
    expected_keys = {
        (original["pending_states"][index]["B"], tuple(original["pending_states"][index]["prefix"]))
        for index in producer["additional_beyond_frozen_six_actual_source_indices"]
    }
    actual_keys = {(row["B"], tuple(row["prefix"])) for row in ledger}
    old_paid_keys = {(row["B"], tuple(row["prefix"])) for row in old_paid}
    if actual_keys != expected_keys or actual_keys & old_paid_keys or len(actual_keys) != 680:
        raise ValueError("midarc filtered source did not isolate the actual NEW680 or re-paid old5546")
    if (
        semantic["all_original_physical_count_AND_shadow_label_cases_checked"] != 9172
        or semantic["new_midarc_boundary_family_counts"] != {"15": 47, "16": 539, "17": 94}
    ):
        raise ValueError("midarc filtered-source case/family totals changed")
    rejected = []

    def reject(name, function, arguments, mutate):
        changed = deepcopy(arguments)
        mutate(changed)
        try:
            function(*changed)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(name)
        else:
            raise AssertionError("invalid midarc filtered-source accounting accepted: " + name)

    bundle = [source, frontier, ledger, constants, proofs]
    reject("duplicate-whole-source-prefix-payment", accounting.partition_gate, bundle,
           lambda rows: rows[2].append(rows[2][0]))
    reject("boolean-source-index", accounting.partition_gate, bundle,
           lambda rows: rows[2][0].update(source_index=True))
    reject("qualifying-whole-prefix-payment-omitted", accounting.partition_gate, bundle,
           lambda rows: rows[2].pop(0))
    reject("original-physical-count-case-omitted", accounting.partition_gate, bundle,
           lambda rows: rows[2][0]["all_original_physical_count_and_shadow_case_distributions"].pop())
    reject("future-outside-original-slots-discarded", accounting.partition_gate, bundle,
           lambda rows: rows[2][0].update(
               outside_budget_INCLUDES_introduced_outside_vertices_AND_future_labels=False))
    reject("first-anchor-frame-substituted-for-midarc", accounting.partition_gate, bundle,
           lambda rows: rows[2][0].update(
               midpoint_of_actual_short_anchor_arc_NOT_first_anchor_frame=False))
    reject("unpaid-sibling-prefix-omitted", accounting.partition_gate, bundle,
           lambda rows: rows[1]["pending_states"].pop())
    reject("paid-prefix-reintroduced-in-filtered-frontier", accounting.partition_gate, bundle,
           lambda rows: rows[1]["pending_states"].append(rows[2][0]["actual_entire_source_state"]))
    reject("old11183-source-family-count-restored", accounting.partition_gate, bundle,
           lambda rows: rows[0]["families"][1].update(pending_subtrees=1224))
    reject("original-U-unconditional-scope-substitution", accounting.partition_gate, bundle,
           lambda rows: rows[0].update(radius_scope="unconditional-original-U"))
    reject("actual-original-source-state-altered", transfer.partition,
           [source, constants, certificates, proofs],
           lambda rows: rows[0]["pending_states"][0].update(
               next=rows[0]["pending_states"][0]["next"]+1))
    reject("continuous-midarc-proof-unbound", transfer.lemma_gate, [certificates, proofs],
           lambda rows: rows[1].pop("midarc"))
    reject("embedded-shadow-original-owner-hypothesis-missing", transfer.lemma_gate,
           [certificates, proofs],
           lambda rows: rows[0]["bridge"]["explicit_ordered_real_hypotheses"].pop())
    # Parent acceptance guard controls use explicit SYNTHETIC minimal headers.
    # They are never written as a completed current or independent final.
    digest = "a" * 64
    parent = {
        "schema": accounting.PARENT_SCHEMA, "files": {"synthetic-proof-NOT-real-file": "b"*64},
        "current_bound_bytes_rechecked": True,
        "prior_completed_full_chain_semantic_replay_still_bound": True,
        "mixed_after_six_actual_completed_parent_pair_bound": True,
        "mixed_curvature_actual_full_semantic_exit_code": 0,
        "mixed_curvature_actual_published_replay_matched_and_semantics_replayed_here": True,
        "all_newest_owned_histories_retained_identically": True,
        "current_transport_frontier_unchanged_by_mixed_candidate_covers": True,
        "candidate_angle_unresolved_closed_boxes": 16,
        "remaining_latest_partial_root_histories": 1,
        "Rstar_conditional_frontier_pending_subtrees": 5637,
        "Rstar_conditional_frontier_families": source["families"],
        "radius_scope": accounting.SCOPE, "r_strict_interval": [
            "0.234700090400448239616790133776692127560495963654971391785924",
            "0.234700090400448239616790133776692127560495963654971391785925",
        ],
        "original_U_current_pending_subtrees_unchanged": 3922,
        "original_52_coordinate_local_allowance_unchanged": "7/800000",
        "joined_closed_full_type_codes_in_these_two_catalogues": 87,
        "all_closed_type_proof_receipts_and_identical_full_graph_radius_classifications_rechecked": 215,
        **{name: False for name in accounting.GLOBAL_FALSE},
        "SYNTHETIC_NOT_completed_current": True,
    }
    final = {
        "schema": accounting.PARENT_FINAL_SCHEMA, "current_audit_sha256": digest,
        "all_current_file_digests_rehashed": True, "current_file_digests_rechecked": 1,
        "actual_completed_SIX_parent_pair_AND_identical_filtered_frontier_bound": True,
        "actual_NEW_current_executor_AND_tested_SIX_identity_adapter_bound": True,
        "mixed_actual_own_acceptance_publication_and_current_semantic_replays_equal": True,
        "all_uncovered_whole_roots_and_latest_partial_histories_retained": True,
        "candidate_angle_unresolved_closed_boxes": 16, "remaining_latest_partial_root_histories": 1,
        "Rstar_conditional_frontier_pending_subtrees": 5637,
        "Rstar_conditional_frontier_families": source["families"],
        "radius_scope": accounting.SCOPE, "r_strict_interval": parent["r_strict_interval"],
        "original_LOCAL_unchanged": "7/800000",
        "retained_closed_full_type_codes": 87, "retained_checked_proof_receipts": 215,
        **{name: False for name in accounting.GLOBAL_FALSE},
        "SYNTHETIC_NOT_completed_independent_final": True,
    }
    accounting.parent_gate(parent, final, digest)
    for name, index, field, value in (
        ("unfinished-independent-mixed-final", 1, "all_current_file_digests_rehashed", False),
        ("older25root-owner-restored", 0, "candidate_angle_unresolved_closed_boxes", 25),
        ("old11183-parent-frontier-restored", 0, "Rstar_conditional_frontier_pending_subtrees", 11183),
        ("full-mixed-main-not-completed", 0, "mixed_curvature_actual_full_semantic_exit_code", 1),
        ("latest-root959-history-discarded", 0, "all_newest_owned_histories_retained_identically", False),
        ("original-LOCAL-allowance-erased", 0, "original_52_coordinate_local_allowance_unchanged", "0"),
        ("historical-proof-receipt-missing", 1, "retained_checked_proof_receipts", 214),
        ("unproved-n26-global-optimality", 0, "global_optimality_proved", True),
    ):
        reject(name, accounting.parent_gate, [parent, final, digest],
               lambda rows, index=index, field=field, value=value: rows[index].update({field: value}))
    if len(rejected) != 21:
        raise AssertionError("midarc remaining-source control count differs: " + str(len(rejected)))
    if any(binding.sha(path) != digest for path, digest in digests.items()):
        raise ValueError("midarc control source/continuous proof/executor changed during complete replay")
    report = {
        "schema": "N26-midarc-SIX-filtered-source-independent-accounting-controls-v1",
        "verified": False, "new_formal_geometric_payments": 0,
        "actual_SIX_geometry_DATA_not_claimed_a_completed_current_parent": True,
        "synthetic_parent_final_headers_NOT_geometry_or_current_acceptance": True,
        "entire_actual5637_ORIGINAL_prefixes_freshly_reconstructed": True,
        "actual_independent_NEW680_source_partition": result,
        "only_remaining680_paid_NOT_old5546_repaid": True,
        "actual_full11183_midarc_classification_matched_by_prefix_identity": True,
        "invalid_controls_rejected": rejected, "input_sha256": digests,
        "actual_SIX_filtered_frontier_sha256": binding.sha(source_path),
        "actual_midarc_full_source_mathematical_controls_sha256": binding.sha(independent_path),
        "tested_transfer_sha256": binding.sha(transfer.__file__),
        "tested_accounting_sha256": binding.sha(accounting.__file__),
        "executed_test_sha256": binding.sha(__file__),
        "new_geometry_own_publication_current_AND_final_STILL_required": True,
        "candidate_whole_roots_removed": 0, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "actual_SIX_filtered_source_midarc_arithmetic_and_accounting_controls_completed": True,
        "source_original_prefixes": 5637, "NEW_prefix_obstructions_NOT_formal_payments": 680,
        "original_physical_and_shadow_cases": 9172, "prospective_frontier_NOT_current": 4957,
        "invalid_controls_rejected": len(rejected), "new_formal_geometric_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
