"""Actual paired878 source and independently reconstructed PHYSICAL donor kernels.

The16 rational physical certificates are reused as data; new physical-only
angle bounds are computed from scratch. No origin certificate is relabelled.
"""

from copy import deepcopy
from fractions import Fraction as F
from pathlib import Path

from audit_prefix_partition import linux
import n26_latest910_shared_origin_source as ancestor
import n26_balanced_correlated_diagonal_suggestion as suggestion
import test_checked_root28_full134rod_intersections as independent_domains
import verify_conditional_force_stage as binding


SEED = Path("outputs/n26-root25-latest878-checked-shared-origin-sweep-composition-v1.json")
CONTROLS = Path("outputs/n26-root25-latest878-checked-shared-origin-sweep-independent-controls-v1.json")
SEED_SHA = "0258d0f045317c03d70aa7bc8b2421460aa441c89020d1f2acbda7edde1b4ef4"
CONTROL_SHA = "2a2e9b277ef99b282eabd62588b1ec4831d9ababbace17d0249354d7a74c71fe"
ORIGIN_KINDS = (*ancestor.ORIGIN_KINDS, "SHARED-FRESH-FULL134-TWO-ORIGIN-BRANCHES-ENERGY")


def scope(seed, controls):
    if (
        seed["schema"] != "N26-unaccepted-latest-root25-checked-shared-origin-support-sweep-composition-v1"
        or controls["schema"] != "N26-independent-latest-root25-checked-shared-origin-support-sweep-composition-v1"
        or controls["diagnosis_sha256"] != SEED_SHA
        or seed["source_OPEN_index"] != 25 or controls["source_OPEN_index"] != 25
        or seed["actual_checked910_predecessor_sha256"] != ancestor.SEED_SHA
        or seed["actual_checked910_controls_sha256"] != ancestor.CONTROL_SHA
        or seed["remaining_OPEN_leaf_count"] != 878 or controls["remaining_OPEN_leaf_count"] != 878
        or seed["total_whole_original_v4_OPEN_leaves_excluded"] != 106
        or controls["total_whole_original_v4_OPEN_leaves_excluded"] != 106
        or len(seed["nodes"]) != 2999 or len(seed["arithmetic_ledger"]) != 622
        or len(seed["fresh_joint_origin_supports"]) != 16
        or controls["all2999_actual_domains_splits_old_supports16_fresh_supports_AND590_old_strict_rows_retained"] is not True
        or controls["complete2539_two_origin_AND2641_origin_forest_ANDprevious8fresh_whole_leaves_retained"] is not True
        or seed["nodes"][2641]["kind"] != ancestor.ancestor.NEW_ANCESTOR_KINDS[1]
        or any(record["verified"] is not False or record["new_geometric_payments"] != 0
               or record["global_lower_bound_proved"] is not False
               or record["global_optimality_proved"] is not False
               or record["n27_started"] is not False for record in (seed, controls))
    ):
        raise ValueError("physical donor source reset paired878 or promoted qualified arithmetic scope")


def inputs():
    initial = ancestor.ancestor.original_source
    original, model, old_bases, v4, v4_controls, row, old_pending, arcs, inventory = initial.source_inputs()
    if binding.sha(SEED) != SEED_SHA or binding.sha(CONTROLS) != CONTROL_SHA:
        raise ValueError("physical donor source changed actual paired878 head")
    seed, controls = binding.read(SEED), binding.read(CONTROLS)
    scope(seed, controls)
    if seed["actual_source_closed_box"] != row or seed["source_file_sha256"] != v4["source_file_sha256"]:
        raise ValueError("physical donor source is not the actual original root25 model")
    initial.mixed.retention_gate(v4, seed)
    for record in (seed, controls):
        for text, digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("physical donor source checked878 prerequisite changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("physical donor original-model digest conflict")
            inventory[text] = digest
    view = [{"kind": "OPEN"} if node["kind"] in ORIGIN_KINDS else deepcopy(node) for node in seed["nodes"]]
    leaves = initial.mixed.partition(original["matrix"], row, view, initial.mixed.old.prior.prior.tighten, False)
    domains, parents = independent_domains.all_domains(original, row, seed["nodes"])
    for leaf in leaves:
        index = leaf["index"]
        leaf["kind"] = seed["nodes"][index]["kind"]
        if domains[index] is not None and domains[index] != (list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))):
            raise ValueError("physical donor source independent entire closed domains differ")
    pending = [leaf for leaf in leaves if leaf["kind"] == "OPEN"]
    paid = {leaf["index"] for leaf in leaves if leaf["kind"] not in ("OPEN", "EMPTY")}
    if (
        pending != seed["pending_closed_leaf_boxes"] or len(pending) != 878
        or paid != {leaf["index"] for leaf in seed["arithmetic_ledger"]}
    ):
        raise ValueError("physical donor source lost an old proof or unproved remainder")
    references = {}
    for node in seed["nodes"]:
        if node["kind"] != ancestor.FRESH_KIND:
            continue
        for proof in node["origin_branch_certificates"]:
            index = proof["fresh_joint_support_index"]
            if type(index) is not int or index in references or not 0 <= index < 16:
                raise ValueError("physical donor reference has ambiguous checked support ownership")
            if proof["origin_center_label"] != seed["fresh_joint_origin_supports"][index]["origin_center_label"]:
                raise ValueError("physical donor reference no longer belongs to the original support")
            references[index] = list(map(F, proof["certificate"]["reference_turns"]))
    if set(references) != set(range(16)):
        raise ValueError("physical donor table is not fully bound to the old sixteen actual supports")
    physical_supports = []
    for index, donor in enumerate(seed["fresh_joint_origin_supports"]):
        if set(donor) != {"origin_center_label", "base_kernel_certificate", "origin_multiplier"}:
            raise ValueError("physical donor table has unknown physical or virtual fields")
        physical_supports.append({
            "mode": initial.mixed.SUPPORT_MODE,
            "kernel_certificate": donor["base_kernel_certificate"],
            "suggestion_point_turns": list(map(str, references[index])),
        })
    # Real NEW physical full134 gates: no augmented origin kernel/flags,
    # no virtual mu, no old origin energy result copied into a physical mode.
    kernels = initial.mixed.full_support_gate(model, physical_supports)
    inventory.update({
        linux(SEED): SEED_SHA, linux(CONTROLS): CONTROL_SHA,
        linux(__file__): binding.sha(__file__),
        linux(independent_domains.__file__): binding.sha(independent_domains.__file__),
        linux(suggestion.__file__): binding.sha(suggestion.__file__),
    })
    return original, model, seed, controls, row, pending, physical_supports, kernels, references, arcs, inventory


def ownership(record, seed, pending):
    by_index = {leaf["index"]: leaf for leaf in pending}
    seen, strict = set(), set()
    for item in record["actual_physical_only_whole_leaf_trials"]:
        leaf, trials = item["actual_latest878_whole_OPEN_leaf"], item["actual_physical_donor_trials"]
        index = leaf["index"]
        if index in seen or by_index.get(index) != leaf or seed["nodes"][index] != {"kind": "OPEN"} or not trials:
            raise ValueError("physical-only target repeated, clipped, paid or from an ancestor")
        seen.add(index)
        proofs = []
        for trial in trials:
            donor, result = trial["physical_donor_index"], trial["arithmetic_result"]
            if type(donor) is not int or not 0 <= donor < 16:
                raise ValueError("physical-only target has an unbound donor index")
            proved = result is not None and result["arithmetic_strict_target_test_passed"] is True
            if trial["strict_entire_physical_only_leaf"] != proved:
                raise ValueError("physical-only target promoted a failed bound")
            if proved:
                if (
                    trial["certificate"] is None or trial["certificate"]["schema"] != suggestion.exact.SCHEMA
                    or F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0
                    or any(name in trial["certificate"] for name in ("origin_center_label", "origin_multiplier"))
                ):
                    raise ValueError("physical-only proof lacks a fresh exact physical-mode entire-domain certificate")
                proofs.append(trial)
        if item["strict_whole_physical_leaf"] != bool(proofs):
            raise ValueError("physical-only target success set differs from actual full-domain trials")
        chosen = item["selected_strict_physical_proof"]
        if (chosen is not None) != bool(proofs) or chosen is not None and chosen not in proofs:
            raise ValueError("physical-only target selected a nonexistent or nonstrict proof")
        if proofs:
            strict.add(index)
    if (
        record["new_strict_whole_leaf_indices"] != sorted(strict)
        or record["prospective_arithmetic_remaining_OPEN_after_independent_join"] != 878-len(strict)
        or record["latest878_global_nodes_and622_strict_rows_UNMODIFIED"] is not True
    ):
        raise ValueError("physical-only whole-leaf count or old proof retention differs")
    return strict
