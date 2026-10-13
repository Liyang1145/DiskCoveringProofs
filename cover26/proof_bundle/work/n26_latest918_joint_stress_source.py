"""Original model and ACTUAL paired918 arithmetic source, not geometry admission.

Old v4 is used only to reconstruct the original physical model. All work
domains come from the checked918 successor; its66 exclusions are retained.
"""

from copy import deepcopy
from fractions import Fraction as F
from pathlib import Path

from audit_prefix_partition import linux
import probe_root25_v4_balanced_whole_leaf_energy as original_source
import test_checked_root28_full134rod_intersections as independent_domains
import verify_conditional_force_stage as binding


SEED = Path("outputs/n26-root25-latest918-checked-origin-forest-composition-v1.json")
CONTROLS = Path("outputs/n26-root25-latest918-checked-origin-forest-independent-controls-v1.json")
SEED_SHA = "4630f1ee82d81e386c7a174fe7ae46f11f6691800d884671bb92213de81cab15"
CONTROL_SHA = "a7ed44c3582808eee85b5ee5a5037f2680512e0ddb6607cec97e5784cf7568ba"
NEW_ANCESTOR_KINDS = (
    "FULL134-TWO-ORIGIN-BRANCHES-ENERGY",
    "FULL134-TWO-ORIGIN-CLOSED-FORESTS-ENERGY",
)


def scope(seed, controls):
    if (
        seed["schema"] != "N26-unaccepted-latest-root25-checked-two-origin-closed-forest-composition-v1"
        or controls["schema"] != "N26-independent-latest-root25-checked-origin-forest-arithmetic-composition-v1"
        or controls["diagnosis_sha256"] != SEED_SHA
        or seed["source_OPEN_index"] != 25 or controls["source_OPEN_index"] != 25
        or seed["remaining_OPEN_leaf_count"] != 918 or controls["remaining_OPEN_leaf_count"] != 918
        or seed["total_whole_original_v4_OPEN_leaves_excluded"] != 66
        or controls["total_whole_original_v4_OPEN_leaves_excluded"] != 66
        or len(seed["nodes"]) != 2999 or len(seed["arithmetic_ledger"]) != 582
        or controls["all2999_actual_closed_domains_splits_supports_AND581_old_strict_rows_independently_retained"] is not True
        or seed["nodes"][2539]["kind"] != NEW_ANCESTOR_KINDS[0]
        or seed["nodes"][2641]["kind"] != NEW_ANCESTOR_KINDS[1]
        or any(record["verified"] is not False or record["new_geometric_payments"] != 0
               or record["global_lower_bound_proved"] is not False
               or record["global_optimality_proved"] is not False
               or record["n27_started"] is not False for record in (seed, controls))
    ):
        raise ValueError("joint-stress source reset checked918 or promoted arithmetic to geometry")


def inputs():
    original, model, bases, v4, v4_controls, row, v4_pending, arcs, inventory = original_source.source_inputs()
    if binding.sha(SEED) != SEED_SHA or binding.sha(CONTROLS) != CONTROL_SHA:
        raise ValueError("actual latest918 composition/control pair changed")
    seed, controls = binding.read(SEED), binding.read(CONTROLS)
    scope(seed, controls)
    if seed["actual_source_closed_box"] != row or seed["source_file_sha256"] != v4["source_file_sha256"]:
        raise ValueError("latest918 is not bound to the reconstructed original root25 model")
    original_source.mixed.retention_gate(v4, seed)
    for record in (seed, controls):
        for text, digest in record["input_sha256"].items():
            if binding.sha(text) != digest:
                raise ValueError("checked918 prerequisite content changed")
            if text in inventory and inventory[text] != digest:
                raise ValueError("checked918 original-model prerequisite digest conflict")
            inventory[text] = digest
    # Partition view ONLY; no old energy dispatcher receives an origin proof.
    view = [
        {"kind": "OPEN"} if node["kind"] in NEW_ANCESTOR_KINDS else deepcopy(node)
        for node in seed["nodes"]
    ]
    mixed = original_source.mixed
    leaves = mixed.partition(original["matrix"], row, view, mixed.old.prior.prior.tighten, False)
    domains, parents = independent_domains.all_domains(original, row, seed["nodes"])
    for leaf in leaves:
        index = leaf["index"]
        leaf["kind"] = seed["nodes"][index]["kind"]
        actual = domains[index]
        if actual is not None and actual != (list(map(F, leaf["lower"])), list(map(F, leaf["upper"]))):
            raise ValueError("latest918 independent full closed-domain reconstruction differs")
    pending = [leaf for leaf in leaves if leaf["kind"] == "OPEN"]
    if pending != seed["pending_closed_leaf_boxes"] or len(pending) != 918:
        raise ValueError("latest918 domain walk omitted or reintroduced a paid region")
    ledger = {leaf["index"]: leaf for leaf in seed["arithmetic_ledger"]}
    paid = {leaf["index"] for leaf in leaves if leaf["kind"] not in ("OPEN", "EMPTY")}
    if len(ledger) != 582 or set(ledger) != paid:
        raise ValueError("latest918 complete strict ledger/domain ownership differs")
    inventory.update({
        linux(SEED): SEED_SHA, linux(CONTROLS): CONTROL_SHA,
        linux(__file__): binding.sha(__file__),
        linux(independent_domains.__file__): binding.sha(independent_domains.__file__),
    })
    return original, model, bases, seed, controls, row, pending, arcs, inventory


def target_gate(record, seed, pending):
    """Whole original OPEN targets only; no successful single branch pays a leaf."""
    by_index = {leaf["index"]: leaf for leaf in pending}
    seen, strict = set(), set()
    for item in record["actual_joint_stress_whole_leaf_trials"]:
        leaf = item["actual_latest918_whole_OPEN_leaf"]
        index = leaf["index"]
        if index in seen or by_index.get(index) != leaf or seed["nodes"][index] != {"kind": "OPEN"}:
            raise ValueError("joint-stress target repeated, paid, clipped or from an older source")
        seen.add(index)
        trials = item["actual_origin_branch_trials"]
        if len(trials) != 2 or {trial["origin_center_label"] for trial in trials} != {16, 25}:
            raise ValueError("joint-stress target omitted a necessary original origin owner")
        owners = set()
        for trial in trials:
            owner = trial["origin_center_label"]
            result = trial["whole_origin_branch_arithmetic_result"]
            proved = result is not None and result["arithmetic_strict_entire_origin_branch"] is True
            if trial["fresh_exact_whole_origin_branch_strict"] != proved:
                raise ValueError("joint stress changed an actual failed/strict branch classification")
            if proved:
                if (
                    trial["whole_origin_branch_certificate"] is None
                    or result["origin_center_label"] != owner
                    or F(result["strict_energy_margin"]) <= 0 or F(result["strict_radius_margin"]) <= 0
                ):
                    raise ValueError("joint stress strict branch lacks an entire-domain strict result")
                owners.add(owner)
        if item["BOTH_whole_origin_branches_strict"] != (owners == {16, 25}):
            raise ValueError("one strict origin branch forged as a whole-leaf exclusion")
        if owners == {16, 25}:
            strict.add(index)
    advertised = record["actual_new_strict_whole_leaf_indices"]
    if (
        advertised != sorted(strict) or len(advertised) != len(set(advertised))
        or record["prospective_arithmetic_remaining_OPEN_after_independent_join"] != 918-len(strict)
        or record["latest918_global_nodes_and582_strict_ledger_rows_UNMODIFIED"] is not True
    ):
        raise ValueError("joint-stress whole-leaf count/retention classification differs")
    return strict
