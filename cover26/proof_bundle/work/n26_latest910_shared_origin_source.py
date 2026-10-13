"""Paired910 whole domains and its16 checked fresh physical/origin supports."""

from copy import deepcopy
from fractions import Fraction as F
from pathlib import Path

from audit_prefix_partition import linux
import n26_latest918_joint_stress_source as ancestor
import n26_origin_branch_correlated_energy as energy
import test_checked_root28_full134rod_intersections as independent_domains
import verify_conditional_force_stage as binding


SEED = Path("outputs/n26-root25-latest910-checked-joint-origin-batch-composition-v1.json")
CONTROLS = Path("outputs/n26-root25-latest910-checked-joint-origin-batch-independent-controls-v1.json")
SEED_SHA = "aad070ed13b708b6cf6979761aaaa156016b6278e928321f61605c7b1115dab0"
CONTROL_SHA = "6c72acdbfa57856b520fe4c0d0add076be5d585ef4b5b28c3aaa10db68b1d226"
FRESH_KIND = "FRESH-FULL134-TWO-ORIGIN-BRANCHES-ENERGY"
ORIGIN_KINDS = (*ancestor.NEW_ANCESTOR_KINDS, FRESH_KIND)


def scope(seed, controls):
    if (
        seed["schema"] != "N26-unaccepted-latest-root25-checked-fresh-joint-origin-batch-composition-v1"
        or controls["schema"] != "N26-independent-latest-root25-checked-fresh-joint-origin-batch-composition-v1"
        or controls["diagnosis_sha256"] != SEED_SHA
        or seed["actual_checked918_predecessor_sha256"] != ancestor.SEED_SHA
        or seed["actual_checked918_controls_sha256"] != ancestor.CONTROL_SHA
        or seed["remaining_OPEN_leaf_count"] != 910 or controls["remaining_OPEN_leaf_count"] != 910
        or seed["total_whole_original_v4_OPEN_leaves_excluded"] != 74
        or controls["total_whole_original_v4_OPEN_leaves_excluded"] != 74
        or len(seed["nodes"]) != 2999 or len(seed["arithmetic_ledger"]) != 590
        or len(seed["fresh_joint_origin_supports"]) != 16
        or seed["new_whole_actual918_OPEN_leaf_indices"] != [1849,1850,1912,2227,2367,2463,2941,2987]
        or controls["all2999_actual_domains_splits_old_supports_AND582_old_strict_rows_retained"] is not True
        or controls["every_new_whole_leaf_binds_BOTH_checked_owners_and_exact_fresh_kernel_supports"] is not True
        or seed["nodes"][2641]["kind"] != ancestor.NEW_ANCESTOR_KINDS[1]
        or any(record["verified"] is not False or record["new_geometric_payments"] != 0
               or record["global_lower_bound_proved"] is not False
               or record["global_optimality_proved"] is not False
               or record["n27_started"] is not False for record in (seed, controls))
    ):
        raise ValueError("shared fresh support sweep reset actual paired910 or old proof history")


def inputs():
    original, model, old_bases, v4, v4_controls, row, old_pending, arcs, inventory = ancestor.original_source.source_inputs()
    if binding.sha(SEED) != SEED_SHA or binding.sha(CONTROLS) != CONTROL_SHA:
        raise ValueError("shared fresh support sweep changed actual paired910 arithmetic source")
    seed, controls = binding.read(SEED), binding.read(CONTROLS)
    scope(seed, controls)
    if seed["actual_source_closed_box"] != row or seed["source_file_sha256"] != v4["source_file_sha256"]:
        raise ValueError("shared fresh support sweep did not reconstruct original root25 physical model")
    ancestor.original_source.mixed.retention_gate(v4, seed)
    for record in (seed, controls):
        for text, digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("paired910 checked arithmetic prerequisite changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("paired910 original model/prerequisite digest conflict")
            inventory[text] = digest
    mixed = ancestor.original_source.mixed
    view = [{"kind": "OPEN"} if node["kind"] in ORIGIN_KINDS else deepcopy(node) for node in seed["nodes"]]
    leaves = mixed.partition(original["matrix"], row, view, mixed.old.prior.prior.tighten, False)
    domains, parents = independent_domains.all_domains(original, row, seed["nodes"])
    for leaf in leaves:
        index = leaf["index"]
        leaf["kind"] = seed["nodes"][index]["kind"]
        if domains[index] is not None and domains[index] != (list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))):
            raise ValueError("paired910 independent closed-domain reconstruction differs")
    pending = [leaf for leaf in leaves if leaf["kind"] == "OPEN"]
    if pending != seed["pending_closed_leaf_boxes"] or len(pending) != 910:
        raise ValueError("shared fresh support sweep omitted or reintroduced a paid whole region")
    bases, kernels, references, used = [], [], {}, set()
    for index, support in enumerate(seed["fresh_joint_origin_supports"]):
        if set(support) != {"origin_center_label", "base_kernel_certificate", "origin_multiplier"}:
            raise ValueError("paired910 fresh support has unlabelled or extra mathematical fields")
        base = energy.scalar.full.kernel_gate(model, support["base_kernel_certificate"])
        kernel = energy.origin.kernel_gate(
            base, original["data"][3], support["origin_center_label"], support["origin_multiplier"])
        bases.append(base)
        kernels.append(kernel)
    for index in seed["new_whole_actual918_OPEN_leaf_indices"]:
        node = seed["nodes"][index]
        if node["kind"] != FRESH_KIND or len(node["origin_branch_certificates"]) != 2:
            raise ValueError("paired910 lost a completed fresh whole-leaf two-owner proof")
        for proof in node["origin_branch_certificates"]:
            support_index = proof["fresh_joint_support_index"]
            if (
                type(support_index) is not int or support_index in used or not 0 <= support_index < 16
                or proof["origin_center_label"] != kernels[support_index]["origin_center_label"]
            ):
                raise ValueError("paired910 fresh support/reference owner binding differs")
            references[support_index] = list(map(F, proof["certificate"]["reference_turns"]))
            used.add(support_index)
    if used != set(range(16)):
        raise ValueError("paired910 fresh support table has an unbound original owner")
    inventory.update({
        linux(SEED): SEED_SHA, linux(CONTROLS): CONTROL_SHA,
        linux(__file__): binding.sha(__file__),
        linux(independent_domains.__file__): binding.sha(independent_domains.__file__),
    })
    return original, model, seed, controls, row, pending, bases, kernels, references, arcs, inventory


def target_gate(record, seed, pending):
    by_index = {leaf["index"]: leaf for leaf in pending}
    seen, strict = set(), set()
    for item in record["actual_shared_fresh_whole_leaf_trials"]:
        leaf = item["actual_latest910_whole_OPEN_leaf"]
        index = leaf["index"]
        if index in seen or by_index.get(index) != leaf or seed["nodes"][index] != {"kind": "OPEN"}:
            raise ValueError("shared fresh support target paid, repeated, clipped or from an old source")
        seen.add(index)
        trials, proofs = item["all_actual_origin_branch_trials"], item["strict_origin_branch_proofs"]
        if not trials or {trial["origin_center_label"] for trial in trials} != {16, 25}:
            raise ValueError("shared fresh support experiment omitted an entire necessary origin owner")
        owners = set()
        for trial in trials:
            support_index, owner = trial["shared_fresh_support_index"], trial["origin_center_label"]
            if (
                type(support_index) is not int or not 0 <= support_index < 16
                or owner not in (16, 25)
                or seed["fresh_joint_origin_supports"][support_index]["origin_center_label"] != owner
            ):
                raise ValueError("shared fresh support trial substituted another origin owner")
            result = trial["arithmetic_result"]
            proved = result is not None and result["arithmetic_strict_entire_origin_branch"] is True
            if trial["whole_actual_origin_branch_strict"] != proved:
                raise ValueError("shared fresh support trial changed failed/strict classification")
            if proved:
                if F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0:
                    raise ValueError("shared fresh support trial has no exact strict entire-domain margin")
                owners.add(owner)
        if (
            any(proof not in trials for proof in proofs)
            or len(proofs) != len({proof["origin_center_label"] for proof in proofs})
            or {proof["origin_center_label"] for proof in proofs} != owners
            or item["BOTH_whole_origin_branches_strict"] != (owners == {16, 25})
        ):
            raise ValueError("shared fresh support one-owner/proof-subset classification differs")
        if owners == {16, 25}:
            strict.add(index)
    if (
        record["actual_new_strict_whole_leaf_indices"] != sorted(strict)
        or record["prospective_arithmetic_remaining_OPEN_after_independent_join"] != 910-len(strict)
        or record["latest910_global_nodes_and590_prior_strict_rows_UNMODIFIED"] is not True
    ):
        raise ValueError("shared fresh support count or latest proof retention differs")
    return strict
